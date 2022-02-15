use clap::Parser;
use space_invaders::cpu;

use cpu::{Address, Byte, Cpu8080, IOManager};

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// ROM to run in the emulator
    rom: std::path::PathBuf,
}

struct IO {
    mem: Vec<cpu::Byte>,
}

impl IO {
    fn new(rom: &[Byte]) -> Self {
        let mut mem = vec![0; 65536];
        mem[..rom.len()].copy_from_slice(rom);
        Self { mem }
    }
}

impl IOManager for IO {
    fn read(&self, addr: Address) -> Byte {
        self.mem[addr as usize]
    }

    fn write(&mut self, addr: Address, byte: Byte) {
        self.mem[addr as usize] = byte;
    }
}

fn main() -> std::io::Result<()> {
    let rom = std::fs::read(Args::parse().rom)?;

    let mut cpu = Cpu8080::new();
    let mut io = IO::new(&rom);

    loop {
        cpu.step(&mut io);
    }
}
