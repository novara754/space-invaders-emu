//! Emulation of the 8080 CPU.
//!
//! See the 8080 Programmer's Manual.

use crate::{console_log, debug_print, debug_println};

/// 8080 byte size
pub type Byte = u8;

/// 8080 word size
pub type Word = u16;

/// 8080 address size
pub type Address = u16;

/// Trait to represent IO interfaces for the CPU (memory, IO ports, etc)
pub trait IOManager {
    fn read(&self, addr: Address) -> Byte;
    fn write(&mut self, addr: Address, byte: Byte);
    fn port_read(&mut self, port: Byte) -> Byte;
    fn port_write(&mut self, port: Byte, byte: Byte);
}

/// Enumeration of 8080 registers
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Register {
    A,
    B,
    C,
    D,
    H,
    E,
    L,
    SP,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum MemReg {
    Memory,
    Register(Register),
}

impl MemReg {
    fn from(n: u8) -> Self {
        if n == 6 {
            MemReg::Memory
        } else {
            MemReg::Register(Register::from(n))
        }
    }
}

impl std::fmt::Debug for MemReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Memory => write!(f, "M"),
            Self::Register(r) => write!(f, "{:?}", r),
        }
    }
}

impl std::convert::From<u8> for Register {
    fn from(n: u8) -> Self {
        use Register::*;
        if n == 7 {
            A
        } else {
            [B, C, D, E, H, L][n as usize]
        }
    }
}

impl Register {
    fn offset(self) -> usize {
        use Register::*;
        match self {
            B => 0,
            C => 1,
            D => 2,
            E => 3,
            H => 4,
            L => 5,
            A => 6,
            _ => panic!("Invalid register"),
        }
    }
}

/// 8080 CPU flags
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Flag {
    C = 1 << 0,
    P = 1 << 2,
    // AC = 1 << 4,
    Z = 1 << 6,
    S = 1 << 7,
}

/// 8080 CPU state
#[derive(Debug, Default)]
pub struct Cpu8080 {
    /// Program counter
    pc: Address,

    /// Stack pointer
    sp: Address,

    /// General purpose registers
    gprs: [Byte; 7],

    /// CPU flags
    flags: Byte,

    /// Interrupt enabled flag
    interrupt_enabled: bool,
}

impl Cpu8080 {
    /// Create a new, blank CPU state
    pub fn new() -> Self {
        Self {
            pc: 0,
            sp: 0,
            gprs: [0; 7],
            flags: 1 << 1,
            interrupt_enabled: false,
        }
    }

    /// Execute a single instruction with the current CPU state
    pub fn step<IO: IOManager>(&mut self, io: &mut IO) {
        debug_print!("{:04X}    ", self.pc);

        let op = self.fetch(io);
        let op_hi = (op >> 4) & 0xF;
        let op_lo = op & 0xF;

        match (op_hi, op_lo) {
            // NOP
            (0x0, 0x0) => {
                debug_println!("NOP");
            }

            // EI
            (0xF, 0xB) => {
                debug_println!("EI");
                self.interrupt_enabled = true;
            }

            //DI
            (0xF, 0x3) => {
                debug_println!("DI");
                self.interrupt_enabled = false;
            }

            // JMP
            (0xC, 0x3) => {
                let addr = self.fetch_word(io);
                self.jump(addr);

                debug_println!("JUMP ${:04X}", addr);
            }

            // JNZ
            (0xC, 0x2) => {
                let addr = self.fetch_word(io);

                debug_println!("JNZ ${:04X}", addr);
                if !self.get_flag(Flag::Z) {
                    self.jump(addr);
                }
            }

            // CALL
            (0xC..=0xF, 0xD) => {
                let addr = self.fetch_word(io);
                self.call(io, addr);
                debug_println!("CALL ${:04X}", addr);
            }

            // RET
            (0xC, 0x9) => {
                debug_println!("RET");
                self.ret(io);
            }

            // RNZ
            (0xC, 0x0) => {
                debug_println!("RNZ");

                if !self.get_flag(Flag::Z) {
                    self.ret(io);
                }
            }

            // CPI
            (0xF, 0xE) => {
                let byte = self.fetch(io);
                debug_println!("CPI #${:02X}", byte);

                let (res, cy) = self.register_read(Register::A).overflowing_sub(byte);
                self.update_flag_z(res);
                self.update_flag_s(res);
                self.update_flag_p(res);
                self.update_flag(Flag::C, cy);
            }

            // LXI
            (0x0..=0x3, 0x1) => {
                use Register::*;
                let dst = [B, D, H, SP][op_hi as usize];
                let word = self.fetch_word(io);
                self.register_write_word(dst, word);

                debug_println!("LXI {:?}, #${:04X}", dst, word);
            }

            // MVI
            (0x0..=0x3, 0x6 | 0xE) => {
                let dst = (op >> 3) & 0x7;
                let byte = self.fetch(io);

                let dst = if dst == 6 {
                    MemReg::Memory
                } else {
                    MemReg::Register(Register::from(dst))
                };
                self.location_write(io, dst, byte);

                debug_println!("MVI {:?}, #${:02X}", dst, byte);
            }

            // MOV
            (0x4..=0x7, lo) => {
                let src = if lo <= 0x7 { lo } else { lo - 0x8 };
                let dst = (op >> 3) & 0x7;

                let dst = if dst == 6 {
                    MemReg::Memory
                } else {
                    MemReg::Register(Register::from(dst))
                };

                let src = if src == 6 {
                    MemReg::Memory
                } else {
                    MemReg::Register(Register::from(src))
                };

                let byte = self.location_read(io, src);
                self.location_write(io, dst, byte);

                debug_println!("MOV {:?}, {:?}", dst, src);
            }

            // LDAX
            (0x0 | 0x1, 0xA) => {
                let reg = [Register::B, Register::D][op_hi as usize];
                let addr = self.register_read_word(reg);
                self.register_write(Register::A, io.read(addr));

                debug_println!("LDAX {:?}", reg);
            }

            // INX
            (0x0..=0x3, 0x3) => {
                use Register::*;
                let dst = [B, D, H, SP][op_hi as usize];
                let word = self.register_read_word(dst);
                self.register_write_word(dst, word.wrapping_add(1));

                debug_println!("INX {:?}", dst);
            }

            // DCR
            (0x0..=0x3, 0x5 | 0xD) => {
                let dst = (op >> 3) & 0x7;
                let dst = if dst == 6 {
                    MemReg::Memory
                } else {
                    MemReg::Register(Register::from(dst))
                };

                let byte = self.location_read(io, dst);
                let new_value = byte.wrapping_sub(1);
                self.location_write(io, dst, new_value);

                self.update_flag_z(new_value);
                self.update_flag_s(new_value);
                self.update_flag_p(new_value);

                debug_println!("DCR {:?}", dst);
            }

            // PUSH
            (0xC..=0xF, 0x5) => {
                use Register::*;
                let src = [B, D, H, A][(op_hi - 0xC) as usize];

                debug_println!("PUSH {:?}", src);

                let word = self.register_read_word(src);
                self.push(io, word);
            }

            // POP
            (0xC..=0xF, 0x1) => {
                use Register::*;
                let dst = [B, D, H, A][(op_hi - 0xC) as usize];

                debug_println!("POP {:?}", dst);

                let word = self.pop(io);
                self.register_write_word(dst, word);
            }

            // DAD
            (0x0..=0x3, 0x9) => {
                use Register::*;
                let src = [B, D, H, SP][op_hi as usize];

                debug_println!("DAD {:?}", src);

                let hl = self.register_read_word(Register::H);
                let word = self.register_read_word(src);
                let (res, cy) = hl.overflowing_add(word);
                self.register_write_word(Register::H, res);
                self.update_flag(Flag::C, cy);
            }

            // XCHG
            (0xE, 0xB) => {
                debug_println!("XCHG");

                let hl = self.register_read_word(Register::H);
                let de = self.register_read_word(Register::D);
                self.register_write_word(Register::H, de);
                self.register_write_word(Register::D, hl);
            }

            // RRC
            (0x0, 0xF) => {
                debug_println!("RRC");

                let a = self.register_read(Register::A);
                let cy = a & 1 > 0;
                self.register_write(Register::A, a.rotate_right(1));
                self.update_flag(Flag::C, cy);
            }

            // ANI
            (0xE, 0x6) => {
                let byte = self.fetch(io);

                debug_println!("ANI #${:02X}", byte);

                let a = self.register_read(Register::A);
                let new_value = a & byte;

                self.register_write(Register::A, new_value);
                self.update_flag_z(new_value);
                self.update_flag_s(new_value);
                self.update_flag_p(new_value);
                self.update_flag(Flag::C, false);
            }

            // ADI
            (0xC, 0x6) => {
                let byte = self.fetch(io);

                debug_println!("ADI #${:02X}", byte);

                let a = self.register_read(Register::A);
                let (new_value, cy) = a.overflowing_add(byte);

                self.register_write(Register::A, new_value);
                self.update_flag_z(new_value);
                self.update_flag_s(new_value);
                self.update_flag_p(new_value);
                self.update_flag(Flag::C, cy);
            }

            // LDA
            (0x3, 0xA) => {
                let addr = self.fetch_word(io);
                debug_println!("LDA ${:04X}", addr);

                self.register_write(Register::A, io.read(addr));
            }

            // STA
            (0x3, 0x2) => {
                let addr = self.fetch_word(io);
                debug_println!("STA ${:04X}", addr);

                io.write(addr, self.register_read(Register::A));
            }

            // ADD, ADC
            (0x8, _) => {
                let is_adc = op_lo >= 0x8;
                let src = if is_adc { op_lo - 0x8 } else { op_lo };
                let src = MemReg::from(src);
                let c_in = is_adc && self.get_flag(Flag::C);
                debug_println!("{} {:?}", if is_adc { "ADC" } else { "ADD" }, src);
                self.arithmetic(io, src, |a, rhs| a.carrying_add(rhs, c_in));
            }

            // SUB, SBB
            (0x9, _) => {
                let is_sbb = op_lo >= 0x8;
                let src = if is_sbb { op_lo - 0x8 } else { op_lo };
                let src = MemReg::from(src);
                let c_in = is_sbb && self.get_flag(Flag::C);
                debug_println!("{} {:?}", if is_sbb { "SBB" } else { "SUB" }, src);
                self.arithmetic(io, src, |a, rhs| a.borrowing_sub(rhs, c_in));
            }

            // ANA
            (0xA, 0x0..=0x7) => {
                let src = MemReg::from(op_lo);
                debug_println!("ANA {:?}", src);
                self.arithmetic(io, src, |a, rhs| (a & rhs, false));
            }

            // XRA
            (0xA, 0x8..=0xF) => {
                let src = MemReg::from(op_lo - 0x8);
                debug_println!("XRA {:?}", src);
                self.arithmetic(io, src, |a, rhs| (a ^ rhs, false));
            }

            // OUT
            (0xD, 0x3) => {
                let port = self.fetch(io);

                debug_println!("OUT #${:02X}", port);

                io.port_write(port, self.register_read(Register::A));
            }

            // IN
            (0xD, 0xB) => {
                let port = self.fetch(io);

                debug_println!("IN #${:02X}", port);

                console_log!("in={}", io.port_read(port));
                self.register_write(Register::A, io.port_read(port));
            }

            _ => {
                debug_println!("UNKNOWN");
                panic!("Unsupported instruction encountered: ${:02X}", op);
            }
        }
    }

    /// Raise an interrupt, which the CPU will start handling with the next `step`
    pub fn raise_int<IO: IOManager>(&mut self, io: &mut IO, int_num: u16) {
        if self.interrupt_enabled {
            debug_println!("RST {}", int_num);
            self.call(io, int_num * 8);
        }
    }

    fn arithmetic<IO: IOManager, F: FnOnce(Byte, Byte) -> (Byte, bool)>(
        &mut self,
        io: &mut IO,
        src: MemReg,
        f: F,
    ) {
        let a = self.register_read(Register::A);
        let rhs = self.location_read(io, src);

        let (new_a, c_out) = f(a, rhs);

        self.register_write(Register::A, new_a);
        self.update_flag_z(new_a);
        self.update_flag_s(new_a);
        self.update_flag_p(new_a);
        self.update_flag(Flag::C, c_out);
    }

    fn update_flag_z(&mut self, value: Byte) {
        self.update_flag(Flag::Z, value == 0);
    }

    fn update_flag_s(&mut self, value: Byte) {
        self.update_flag(Flag::S, value & (1 << 7) > 0);
    }

    fn update_flag_p(&mut self, value: Byte) {
        self.update_flag(Flag::P, value.count_ones() % 2 == 0);
    }

    /// Set a CPU flag to the given value
    fn update_flag(&mut self, flag: Flag, value: bool) {
        if value {
            self.flags |= flag as Byte;
        } else {
            self.flags &= !(flag as Byte);
        }
    }

    /// Get the value of a CPU flag
    fn get_flag(&mut self, flag: Flag) -> bool {
        (self.flags & (flag as Byte)) != 0
    }

    /// Move data into a register or memory location (for MOV, MVI, etc)
    fn location_write<IO: IOManager>(&mut self, io: &mut IO, dst: MemReg, byte: Byte) {
        match dst {
            MemReg::Memory => {
                let addr = self.register_read_word(Register::H);
                io.write(addr, byte);
            }
            MemReg::Register(r) => {
                self.register_write(r, byte);
            }
        }
    }

    /// Move data from a register or memory location (for MOV, MVI, etc)
    fn location_read<IO: IOManager>(&mut self, io: &mut IO, src: MemReg) -> Byte {
        match src {
            MemReg::Memory => {
                let addr = self.register_read_word(Register::H);
                io.read(addr)
            }
            MemReg::Register(r) => self.register_read(r),
        }
    }

    /// Perform a jump
    fn jump(&mut self, addr: Address) {
        self.pc = addr;
    }

    /// Perform a call to a subroutine, saving the return address
    fn call<IO: IOManager>(&mut self, io: &mut IO, addr: Address) {
        self.push(io, self.pc);
        self.jump(addr);
    }

    /// Perform a return from subroutine
    fn ret<IO: IOManager>(&mut self, io: &mut IO) {
        let addr = self.pop(io);
        self.jump(addr);
    }

    /// Push a word onto the stack
    fn push<IO: IOManager>(&mut self, io: &mut IO, word: Word) {
        for b in word.to_be_bytes() {
            io.write(self.sp, b);
            self.sp -= 1;
        }
    }

    /// Pop a word from the stack
    fn pop<IO: IOManager>(&mut self, io: &IO) -> Word {
        u16::from_le_bytes([(); 2].map(|_| {
            self.sp += 1;
            io.read(self.sp)
        }))
    }

    /// Fetch a single byte from memory indexed by the program counter and then
    /// increment the program counter
    fn fetch<IO: IOManager>(&mut self, io: &IO) -> Byte {
        let word = io.read(self.pc);
        self.pc += 1;
        word
    }

    /// Fetch a word from memory indexed by the program counter and then
    /// increment the program counter accordingly
    fn fetch_word<IO: IOManager>(&mut self, io: &IO) -> Word {
        let lo = self.fetch(io);
        let hi = self.fetch(io);
        u16::from_be_bytes([hi, lo])
    }

    /// Write a word to the register pairs
    fn register_write_word(&mut self, dst: Register, word: Word) {
        use Register::*;

        let [hi, lo] = word.to_be_bytes();

        match dst {
            B => {
                self.register_write(B, hi);
                self.register_write(C, lo);
            }
            D => {
                self.register_write(D, hi);
                self.register_write(E, lo);
            }
            H => {
                self.register_write(H, hi);
                self.register_write(L, lo);
            }
            A => {
                self.register_write(A, hi);
                self.flags = lo;
            }
            SP => self.sp = word,
            _ => panic!("Invalid register pair `{:?}'", dst),
        }
    }

    /// Write a byte to a register
    fn register_write(&mut self, dst: Register, byte: Byte) {
        self.gprs[dst.offset()] = byte;
    }

    /// Read a word from a register pair
    fn register_read_word(&mut self, src: Register) -> Word {
        use Register::*;

        match src {
            B => {
                let hi = self.register_read(B);
                let lo = self.register_read(C);
                u16::from_be_bytes([hi, lo])
            }
            D => {
                let hi = self.register_read(D);
                let lo = self.register_read(E);
                u16::from_be_bytes([hi, lo])
            }
            H => {
                let hi = self.register_read(H);
                let lo = self.register_read(L);
                u16::from_be_bytes([hi, lo])
            }
            A => {
                let hi = self.register_read(A);
                let lo = self.flags;
                u16::from_be_bytes([hi, lo])
            }
            SP => self.sp,
            _ => panic!("Invalid register pair `{:?}'", src),
        }
    }

    /// Read a byte from a register
    fn register_read(&mut self, src: Register) -> Byte {
        self.gprs[src.offset()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestIO {
        mem: Vec<Byte>,
    }

    impl IOManager for TestIO {
        fn read(&self, addr: Address) -> Byte {
            self.mem[addr as usize]
        }

        fn write(&mut self, addr: Address, byte: Byte) {
            self.mem[addr as usize] = byte;
        }

        fn port_read(&mut self, _port: Byte) -> Byte {
            0x00
        }

        fn port_write(&mut self, _port: Byte, _byte: Byte) {
            ()
        }
    }

    fn make_test_cpu(code: Vec<Byte>, size: Option<usize>) -> (Cpu8080, TestIO) {
        let mut mem = vec![0u8; size.unwrap_or(code.len())];
        mem[..code.len()].copy_from_slice(&code);
        (Cpu8080::new(), TestIO { mem })
    }

    #[test]
    fn inst_jmp() {
        {
            let (mut cpu, mut io) = make_test_cpu(vec![0xC3, 0x10, 0x00], None);
            assert_eq!(cpu.pc, 0x0000, "old pc");
            cpu.step(&mut io);
            assert_eq!(cpu.pc, 0x0010, "new pc");
        }

        {
            let (mut cpu, mut io) = make_test_cpu(vec![0xC3, 0xCD, 0xAB], None);
            assert_eq!(cpu.pc, 0x0000, "old pc");
            cpu.step(&mut io);
            assert_eq!(cpu.pc, 0xABCD, "new pc");
        }
    }

    #[test]
    fn inst_jnz() {
        for addr in [0xABCDu16, 0x1000] {
            for (z, exp_pc) in [(true, 0x0003), (false, addr)] {
                let [hi, lo] = addr.to_be_bytes();
                let (mut cpu, mut io) = make_test_cpu(vec![0xC2, lo, hi], None);
                cpu.update_flag(Flag::Z, z);
                cpu.step(&mut io);
                assert_eq!(cpu.pc, exp_pc);
            }
        }
    }

    #[test]
    fn inst_call() {
        {
            let (mut cpu, mut io) = make_test_cpu(vec![0xCD, 0x10, 0x00], Some(0x100));
            cpu.sp = 0x0FF;
            cpu.step(&mut io);
            assert_eq!(cpu.pc, 0x0010, "new pc");
            assert_eq!(io.read(cpu.sp + 2), 0x00, "return address hi");
            assert_eq!(io.read(cpu.sp + 1), 0x03, "return address lo");
        }

        {
            let (mut cpu, mut io) = make_test_cpu(vec![0xCD, 0xCD, 0xAB], Some(0x100));
            cpu.sp = 0x0FF;
            assert_eq!(cpu.pc, 0x0000);
            cpu.step(&mut io);
            assert_eq!(cpu.pc, 0xABCD, "new pc");
            assert_eq!(io.read(cpu.sp + 2), 0x00, "return address hi");
            assert_eq!(io.read(cpu.sp + 1), 0x03, "return address lo");
        }
    }

    #[test]
    fn inst_ret() {
        for addr in [0xABCD, 0x1000, 0x0000] {
            let (mut cpu, mut io) = make_test_cpu(vec![0xC9], Some(0x100));
            cpu.sp = 0xFF;
            cpu.push(&mut io, addr);
            cpu.step(&mut io);
            assert_eq!(cpu.pc, addr);
        }
    }

    #[test]
    fn inst_rnz() {
        for addr in [0xABCD, 0x1000, 0x0000] {
            for (z, exp_pc) in [(false, addr), (true, 0x0001)] {
                let (mut cpu, mut io) = make_test_cpu(vec![0xC0], Some(0x100));
                cpu.sp = 0xFF;
                cpu.update_flag(Flag::Z, z);
                cpu.push(&mut io, addr);
                cpu.step(&mut io);
                assert_eq!(cpu.pc, exp_pc, "addr={:04X}, z={}", addr, z);
            }
        }
    }

    #[test]
    fn inst_cpi() {
        for (val, cmp_val, z, s, c, p) in [
            (10, 10, true, false, false, true),
            (10, 5, false, false, false, true),
            (10, 15, false, true, true, false),
        ] {
            let (mut cpu, mut io) = make_test_cpu(vec![0xFE, cmp_val], None);
            cpu.register_write(Register::A, val);
            cpu.step(&mut io);
            assert_eq!(cpu.get_flag(Flag::Z), z, "{} = {}, Z", val, cmp_val);
            assert_eq!(cpu.get_flag(Flag::S), s, "{} = {}, S", val, cmp_val);
            assert_eq!(cpu.get_flag(Flag::C), c, "{} = {}, C", val, cmp_val);
            assert_eq!(cpu.get_flag(Flag::P), p, "{} = {}, P", val, cmp_val);
        }
    }

    #[test]
    fn inst_lxi() {
        use Register::*;
        for (reg, lxi) in [(B, 0x01u8), (D, 0x11), (H, 0x21), (SP, 0x31)] {
            for val in [0x0000u16, 0xABCD, 0x1000] {
                let [hi, lo] = val.to_be_bytes();
                let (mut cpu, mut io) = make_test_cpu(vec![lxi, lo, hi], None);
                cpu.step(&mut io);
                assert_eq!(
                    cpu.register_read_word(reg),
                    val,
                    "LXI {:?}, #${:04X}",
                    reg,
                    val
                );
            }
        }
    }

    #[test]
    fn inst_mvi() {
        use Register::*;
        let vals = [0x00u8, 0xAB, 0x10];

        for (reg, mvi) in [
            (B, 0x06u8),
            (D, 0x16),
            (H, 0x26),
            (C, 0x0E),
            (E, 0x1E),
            (L, 0x2E),
            (A, 0x3E),
        ] {
            for val in vals {
                let (mut cpu, mut io) = make_test_cpu(vec![mvi, val], None);
                cpu.step(&mut io);
                assert_eq!(cpu.register_read(reg), val, "MVI {:?}, #${:02X}", reg, val);
            }
        }

        for val in vals {
            let (mut cpu, mut io) = make_test_cpu(vec![0x36, val], Some(10));
            cpu.register_write_word(Register::H, 0x0002);
            cpu.step(&mut io);
            assert_eq!(io.read(0x0002), val, "MVI M, #${:02X}", val);
        }
    }

    #[test]
    fn inst_mov() {
        let locs = [
            MemReg::Register(Register::B),
            MemReg::Register(Register::C),
            MemReg::Register(Register::D),
            MemReg::Register(Register::E),
            MemReg::Register(Register::H),
            MemReg::Register(Register::L),
            MemReg::Memory,
            MemReg::Register(Register::A),
        ];

        let mut ops = vec![];
        for (i, dst) in locs.into_iter().enumerate() {
            for (j, src) in locs.into_iter().enumerate() {
                if src == dst && src == MemReg::Memory {
                    continue;
                }

                let op = 0x40u8 + (j as u8) + (i as u8) * 0x8;
                ops.push((dst, src, op));
            }
        }

        for (dst, src, op) in ops {
            for val in [0x00, 0x10, 0xAB] {
                let (mut cpu, mut io) = make_test_cpu(vec![op], Some(65536));
                io.write(0x0010, val);
                cpu.register_write_word(Register::H, 0x0010);
                cpu.location_write(&mut io, src, val);
                cpu.step(&mut io);
                assert_eq!(
                    cpu.location_read(&mut io, dst),
                    val,
                    "({:02X}) MOV {:?}, {:?}",
                    op,
                    dst,
                    src
                );
            }
        }
    }

    #[test]
    fn inst_ldax() {
        for (reg, ldax) in [(Register::B, 0x0A), (Register::D, 0x1A)] {
            for val in [0x00, 0x10, 0xAF] {
                let (mut cpu, mut io) = make_test_cpu(vec![ldax], Some(0x20));
                io.write(0x0010, val);
                cpu.register_write_word(reg, 0x0010);
                cpu.step(&mut io);
                assert_eq!(cpu.register_read(Register::A), val, "acc value");
            }
        }
    }

    #[test]
    fn inst_inx() {
        use Register::*;
        for (reg, inx) in [(B, 0x03), (D, 0x13), (H, 0x23), (SP, 0x33)] {
            for (val, exp) in [(0, 1), (65535, 0), (10, 11)] {
                let (mut cpu, mut io) = make_test_cpu(vec![inx], None);
                cpu.register_write_word(reg, val);
                cpu.step(&mut io);
                assert_eq!(
                    cpu.register_read_word(reg),
                    exp,
                    "INX {:?} ({} -> {})",
                    reg,
                    val,
                    exp
                );
            }
        }
    }

    #[test]
    fn inst_dcr() {
        use super::Register::*;
        use MemReg::*;

        for (loc, dcr) in [
            (Register(B), 0x05),
            (Register(C), 0x0D),
            (Register(D), 0x15),
            (Register(E), 0x1D),
            (Register(H), 0x25),
            (Register(L), 0x2D),
            (Memory, 0x35),
            (Register(A), 0x3D),
        ] {
            for (val, exp, z, s, p) in [
                (0, 255, false, true, true),
                (255, 254, false, true, false),
                (1, 0, true, false, true),
            ] {
                let (mut cpu, mut io) = make_test_cpu(vec![dcr], Some(0x20));
                cpu.register_write_word(H, 0x0010);
                cpu.location_write(&mut io, loc, val);
                cpu.step(&mut io);
                assert_eq!(
                    cpu.location_read(&mut io, loc),
                    exp,
                    "DCR {:?} ({} -> {})",
                    loc,
                    val,
                    exp
                );
                assert_eq!(cpu.get_flag(Flag::Z), z, "Z");
                assert_eq!(cpu.get_flag(Flag::S), s, "S");
                assert_eq!(cpu.get_flag(Flag::P), p, "P");
            }
        }
    }

    #[test]
    fn inst_push_pop() {
        use Register::*;
        for (reg, push, pop) in [
            (B, 0xC5, 0xC1),
            (D, 0xD5, 0xD1),
            (H, 0xE5, 0xE1),
            (A, 0xF5, 0xF1),
        ] {
            for val in [0xABCDu16, 0x0000, 0x1000] {
                let (mut cpu, mut io) = make_test_cpu(vec![push, pop], Some(0x100));
                let [hi, lo] = val.to_be_bytes();

                cpu.sp = 0xFF;
                cpu.register_write_word(reg, val);

                cpu.step(&mut io);
                assert_eq!(io.read(cpu.sp + 1), lo, "PUSH {:?} (val={:04X})", reg, val);
                assert_eq!(io.read(cpu.sp + 2), hi, "PUSH {:?} (val={:04X})", reg, val);

                // overwrite with dummy value
                cpu.register_write_word(reg, 0xD8D8);

                cpu.step(&mut io);

                assert_eq!(cpu.register_read_word(reg), val, "POP {:?}", reg,);
            }
        }
    }

    #[test]
    fn inst_dad() {
        use Register::*;
        let vals = [0xABCD, 0x0000, 0x1000];
        for (reg, dad) in [(B, 0x09), (D, 0x19), (H, 0x29), (SP, 0x39)] {
            for hl in vals {
                for val in vals {
                    let (mut cpu, mut io) = make_test_cpu(vec![dad], None);
                    cpu.register_write_word(H, hl);
                    cpu.register_write_word(reg, val);

                    cpu.step(&mut io);

                    let (res, cy) = if reg != H {
                        val.overflowing_add(hl)
                    } else {
                        val.overflowing_add(val)
                    };
                    assert_eq!(
                        cpu.register_read_word(H),
                        res,
                        "DAD {:?} (hl={:04X}, val={:04X})",
                        reg,
                        hl,
                        val
                    );
                    assert_eq!(
                        cpu.get_flag(Flag::C),
                        cy,
                        "DAD {:?} (hl={:04X}, val={:04X})",
                        reg,
                        hl,
                        val
                    );
                }
            }
        }
    }

    #[test]
    fn inst_xchg() {
        use Register::*;
        let vals = [0xABCD, 0x1000, 0x0000, 0x0001];
        for hl in vals {
            for de in vals {
                let (mut cpu, mut io) = make_test_cpu(vec![0xEB], None);
                cpu.register_write_word(H, hl);
                cpu.register_write_word(D, de);

                cpu.step(&mut io);

                assert_eq!(cpu.register_read_word(H), de, "hl={:04X}, de={:04}", hl, de);
                assert_eq!(cpu.register_read_word(D), hl, "hl={:04X}, de={:04}", hl, de);
            }
        }
    }

    #[test]
    fn inst_rrc() {
        let val = 0b1110_1010;
        let cys = [false, true, false, true, false, true, true, true];

        let (mut cpu, mut io) = make_test_cpu(vec![0x0F; 8], None);
        cpu.register_write(Register::A, val);
        for (i, cy) in cys.into_iter().enumerate() {
            cpu.step(&mut io);
            assert_eq!(
                cpu.register_read(Register::A),
                val.rotate_right(i as u32 + 1)
            );
            assert_eq!(cpu.get_flag(Flag::C), cy);
        }
    }

    #[test]
    fn inst_ani() {
        let vals = [0xAB, 0xCD, 0x10, 0x00, 0xF7];
        for a in vals {
            for val in vals {
                let (mut cpu, mut io) = make_test_cpu(vec![0xE6, val], None);
                cpu.register_write(Register::A, a);
                cpu.step(&mut io);
                let new_val = val & a;

                assert_eq!(
                    cpu.register_read(Register::A),
                    new_val,
                    "a={:02X}, val={:02X}",
                    a,
                    val
                );
            }
        }
    }

    #[test]
    fn inst_adi() {
        let vals = [0xAB, 0xCD, 0x10, 0x00, 0xF7];
        for a in vals {
            for val in vals {
                let (mut cpu, mut io) = make_test_cpu(vec![0xC6, val], None);
                cpu.register_write(Register::A, a);
                cpu.step(&mut io);
                let new_val = a.wrapping_add(val);

                assert_eq!(
                    cpu.register_read(Register::A),
                    new_val,
                    "a={:02X}, val={:02X}",
                    a,
                    val
                );
            }
        }
    }

    #[test]
    fn inst_sta_lda() {
        let addr = 0x1FF0u16;
        for val in [0xAB, 0xF8, 0x00, 0x01] {
            let [addr_hi, addr_lo] = addr.to_be_bytes();
            let (mut cpu, mut io) = make_test_cpu(
                vec![0x32, addr_lo, addr_hi, 0x3A, addr_lo, addr_hi],
                Some(addr as usize + 1),
            );
            cpu.register_write(Register::A, val);

            cpu.step(&mut io);
            assert_eq!(io.read(addr), val);

            // Overwrite A with dummy value
            cpu.register_write(Register::A, 0xD8);

            cpu.step(&mut io);
            assert_eq!(cpu.register_read(Register::A), val);
        }
    }

    #[test]
    fn inst_add() {
        let tests = [
            (0x00, 0x00, 0x00, true, false, false),
            (0xFF, 0x01, 0x00, true, false, true),
            (0x7F, 0x01, 0x80, false, true, false),
            (0x10, 0x02, 0x12, false, false, false),
        ];

        for test @ (a, rhs, res, z, s, c_out) in tests {
            for loc in 0..=6 {
                let op = 0x80 + loc;
                let loc = MemReg::from(loc);
                let (mut cpu, mut io) = make_test_cpu(vec![op], Some(0x100));

                cpu.register_write(Register::A, a);
                cpu.register_write_word(Register::H, 0x00FF);
                cpu.location_write(&mut io, loc, rhs);

                cpu.step(&mut io);

                assert_eq!(cpu.register_read(Register::A), res, "{:?}", test);
                assert_eq!(cpu.get_flag(Flag::Z), z, "{:?} Z", test);
                assert_eq!(cpu.get_flag(Flag::S), s, "{:?} S", test);
                assert_eq!(cpu.get_flag(Flag::C), c_out, "{:?} C", test);
            }
        }
    }

    #[test]
    fn inst_adc() {
        let tests = [
            (0x00, 0x00, false, 0x00, true, false, false),
            (0x00, 0x00, true, 0x01, false, false, false),
            (0xFF, 0x01, false, 0x00, true, false, true),
            (0xFF, 0x01, true, 0x01, false, false, true),
            (0xFF, 0x00, false, 0xFF, false, true, false),
            (0xFF, 0x00, true, 0x00, true, false, true),
            (0x7F, 0x01, false, 0x80, false, true, false),
            (0x7F, 0x01, true, 0x81, false, true, false),
            (0x10, 0x02, false, 0x12, false, false, false),
            (0x10, 0x02, true, 0x13, false, false, false),
        ];

        for test @ (a, rhs, c_in, res, z, s, c_out) in tests {
            for loc in 0..=6 {
                let op = 0x88 + loc;
                let loc = MemReg::from(loc);
                let (mut cpu, mut io) = make_test_cpu(vec![op], Some(0x100));

                cpu.update_flag(Flag::C, c_in);
                cpu.register_write(Register::A, a);
                cpu.register_write_word(Register::H, 0x00FF);
                cpu.location_write(&mut io, loc, rhs);

                cpu.step(&mut io);

                assert_eq!(cpu.register_read(Register::A), res, "{:?}", test);
                assert_eq!(cpu.get_flag(Flag::Z), z, "{:?} Z", test);
                assert_eq!(cpu.get_flag(Flag::S), s, "{:?} S", test);
                assert_eq!(cpu.get_flag(Flag::C), c_out, "{:?} C", test);
            }
        }
    }

    #[test]
    fn inst_sub() {
        let tests = [
            (0x00, 0x00, 0x00, true, false, false),
            (0xFF, 0x01, 0xFE, false, true, false),
            (0xFF, 0x00, 0xFF, false, true, false),
            (0x80, 0x01, 0x7F, false, false, false),
            (0x10, 0x02, 0x0E, false, false, false),
        ];

        for test @ (a, rhs, res, z, s, c_out) in tests {
            for loc in 0..=6 {
                let op = 0x90 + loc;
                let loc = MemReg::from(loc);
                let (mut cpu, mut io) = make_test_cpu(vec![op], Some(0x100));

                cpu.register_write(Register::A, a);
                cpu.register_write_word(Register::H, 0x00FF);
                cpu.location_write(&mut io, loc, rhs);

                cpu.step(&mut io);

                assert_eq!(cpu.register_read(Register::A), res, "{:?}", test);
                assert_eq!(cpu.get_flag(Flag::Z), z, "{:?} Z", test);
                assert_eq!(cpu.get_flag(Flag::S), s, "{:?} S", test);
                assert_eq!(cpu.get_flag(Flag::C), c_out, "{:?} C", test);
            }
        }
    }

    #[test]
    fn inst_sbb() {
        let tests = [
            (0x00, 0x00, false, 0x00, true, false, false),
            (0x00, 0x00, true, 0xFF, false, true, true),
            (0xFF, 0x01, false, 0xFE, false, true, false),
            (0xFF, 0x01, true, 0xFD, false, true, false),
            (0xFF, 0x00, false, 0xFF, false, true, false),
            (0xFF, 0x00, true, 0xFE, false, true, false),
            (0x80, 0x01, false, 0x7F, false, false, false),
            (0x80, 0x01, true, 0x7E, false, false, false),
            (0x10, 0x02, false, 0x0E, false, false, false),
            (0x10, 0x02, true, 0x0D, false, false, false),
        ];

        for test @ (a, rhs, c_in, res, z, s, c_out) in tests {
            for loc in 0..=6 {
                let op = 0x98 + loc;
                let loc = MemReg::from(loc);
                let (mut cpu, mut io) = make_test_cpu(vec![op], Some(0x100));

                cpu.update_flag(Flag::C, c_in);
                cpu.register_write(Register::A, a);
                cpu.register_write_word(Register::H, 0x00FF);
                cpu.location_write(&mut io, loc, rhs);

                cpu.step(&mut io);

                assert_eq!(cpu.register_read(Register::A), res, "{:?}", test);
                assert_eq!(cpu.get_flag(Flag::Z), z, "{:?} Z", test);
                assert_eq!(cpu.get_flag(Flag::S), s, "{:?} S", test);
                assert_eq!(cpu.get_flag(Flag::C), c_out, "{:?} C", test);
            }
        }
    }

    #[test]
    fn inst_ana() {
        let tests = [
            (0x00, 0x00, 0x00, true, false),
            (0xFF, 0x01, 0x01, false, false),
            (0xFF, 0x00, 0x00, true, false),
            (0x8C, 0x0F, 0x0C, false, false),
            (0x8C, 0xFF, 0x8C, false, true),
        ];

        for test @ (a, rhs, res, z, s) in tests {
            for loc in 0..=6 {
                let op = 0xA0 + loc;
                let loc = MemReg::from(loc);
                let (mut cpu, mut io) = make_test_cpu(vec![op], Some(0x100));

                cpu.register_write(Register::A, a);
                cpu.register_write_word(Register::H, 0x00FF);
                cpu.location_write(&mut io, loc, rhs);

                cpu.step(&mut io);

                assert_eq!(cpu.register_read(Register::A), res, "{:?}", test);
                assert_eq!(cpu.get_flag(Flag::Z), z, "{:?} Z", test);
                assert_eq!(cpu.get_flag(Flag::S), s, "{:?} S", test);
                assert!(!cpu.get_flag(Flag::C), "{:?} C", test);
            }
        }
    }

    #[test]
    fn inst_xra() {
        let tests = [
            (0x00, 0x00, 0x00, true, false),
            (0xFF, 0x01, 0xFE, false, true),
            (0xFF, 0xFF, 0x00, true, false),
            (0xFF, 0x00, 0xFF, false, true),
            (0x8C, 0x0F, 0x83, false, true),
            (0x8C, 0xFF, 0x73, false, false),
        ];

        for test @ (a, rhs, res, z, s) in tests {
            for loc in 0..=6 {
                let op = 0xA8 + loc;
                let loc = MemReg::from(loc);
                let (mut cpu, mut io) = make_test_cpu(vec![op], Some(0x100));

                cpu.register_write(Register::A, a);
                cpu.register_write_word(Register::H, 0x00FF);
                cpu.location_write(&mut io, loc, rhs);

                cpu.step(&mut io);

                assert_eq!(cpu.register_read(Register::A), res, "{:?}", test);
                assert_eq!(cpu.get_flag(Flag::Z), z, "{:?} Z", test);
                assert_eq!(cpu.get_flag(Flag::S), s, "{:?} S", test);
                assert!(!cpu.get_flag(Flag::C), "{:?} C", test);
            }
        }
    }
}
