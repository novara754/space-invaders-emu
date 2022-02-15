//! Emulation of the 8080 CPU.
//!
//! See the 8080 Programmer's Manual.

use crate::{debug_print, debug_println};

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
}

impl Cpu8080 {
    /// Create a new, blank CPU state
    pub fn new() -> Self {
        Self::default()
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

            // JMP
            (0xC, 0x3) => {
                let addr = self.fetch_word(io);
                self.jump(addr);

                debug_println!("JUMP ${:04X}", addr);
            }

            // CALL
            (0xC..=0xF, 0xD) => {
                let addr = self.fetch_word(io);
                self.push_word(io, self.pc);
                self.jump(addr);

                debug_println!("CALL ${:04X}", addr);
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
                self.move_to(io, dst, byte);

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

                let byte = self.move_from(io, src);
                self.move_to(io, dst, byte);

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
            }

            _ => {
                debug_println!("UNKNOWN");
                panic!("Unsupported instruction encountered: ${:02X}", op);
            }
        }
    }

    /// Move data into a register or memory location (for MOV, MVI, etc)
    fn move_to<IO: IOManager>(&mut self, io: &mut IO, dst: MemReg, byte: Byte) {
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
    fn move_from<IO: IOManager>(&mut self, io: &mut IO, src: MemReg) -> Byte {
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

    /// Push a word onto the stack
    fn push_word<IO: IOManager>(&mut self, io: &mut IO, word: Word) {
        for b in word.to_be_bytes() {
            io.write(self.sp, b);
            self.sp -= 1;
        }
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
                cpu.move_to(&mut io, src, val);
                cpu.step(&mut io);
                assert_eq!(
                    cpu.move_from(&mut io, dst),
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
}
