use clap::Parser;
use eyre::{Context, Report, Result};
use sdl2::{event::Event, pixels::Color};
use space_invaders::cpu;

use cpu::{Address, Byte, Cpu8080, IOManager};

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// ROM to run in the emulator
    rom: std::path::PathBuf,

    /// Start address of the ROM
    #[clap(short, long, default_value = "0")]
    org: String,
}

struct IO {
    rom: Vec<Byte>,
    ram: Vec<Byte>,
    vram: Vec<Byte>,
    wrote_vram: bool,

    shift_reg_hi: Byte,
    shift_reg_lo: Byte,
    shift_offset: Byte,

    buttons1: Byte,
    buttons2: Byte,
}

impl IO {
    pub fn new(org: usize, rom: &[Byte]) -> Self {
        let mut rom_ = vec![0; 0x2000];
        rom_[org..][..rom.len()].copy_from_slice(rom);
        let ram = vec![0; 0x23FF - 0x2000 + 1];
        let vram = vec![0; 0x3FFF - 0x2400 + 1];
        Self {
            rom: rom_,
            ram,
            vram,
            wrote_vram: false,

            shift_reg_hi: 0,
            shift_reg_lo: 0,
            shift_offset: 0,

            buttons1: 0x01,
            buttons2: 0x00,
        }
    }
}

impl IOManager for IO {
    fn read(&self, addr: Address) -> Byte {
        match addr {
            0x0000..=0x1FFF => self.rom[addr as usize],
            0x2000..=0x23FF => self.ram[(addr - 0x2000) as usize],
            0x2400..=0x3FFF => self.vram[(addr - 0x2400) as usize],
            // RAM mirror
            _ => self.ram[(addr - 0x4000) as usize],
        }
    }

    fn write(&mut self, addr: Address, byte: Byte) {
        match addr {
            0x0000..=0x1FFF => self.rom[addr as usize] = byte,
            0x2000..=0x23FF => self.ram[(addr - 0x2000) as usize] = byte,
            0x2400..=0x3FFF => {
                self.vram[(addr - 0x2400) as usize] = byte;
                self.wrote_vram = true;
            }
            // RAM mirror
            _ => self.ram[(addr - 0x4000) as usize] = byte,
        }
    }

    fn port_read(&mut self, port: Byte) -> Byte {
        match port {
            0x01 => self.buttons1,
            0x02 => self.buttons2,
            0x03 => {
                let shift_reg = u16::from_be_bytes([self.shift_reg_hi, self.shift_reg_lo]);
                let result = (shift_reg >> (8 - self.shift_offset)) & 0xFF;
                result as u8
            }
            _ => unreachable!(),
        }
    }

    fn port_write(&mut self, port: Byte, byte: Byte) {
        match port {
            0x02 => {
                self.shift_offset = byte & 0x07;
            }
            0x04 => {
                self.shift_reg_lo = self.shift_reg_hi;
                self.shift_reg_hi = byte;
            }
            _ => {}
        }
    }
}

fn draw(io: &IO, canvas: &mut sdl2::render::Canvas<sdl2::video::Window>) -> Result<()> {
    const SCREEN_HEIGHT: usize = 256;
    const SCREEN_WIDTH: usize = 224;

    let mut img = [0u8; SCREEN_HEIGHT * SCREEN_WIDTH * 3];

    let bytes_per_row = SCREEN_HEIGHT / 8;
    for data_y in 0..SCREEN_WIDTH {
        for data_x in 0..bytes_per_row {
            let byte_idx = data_y * bytes_per_row + data_x;
            let byte = io.vram[byte_idx];

            for bit_idx in 0..8 {
                let bit = (byte >> bit_idx) & 1;

                let img_y = SCREEN_HEIGHT - 1 - (data_x * 8 + bit_idx);
                let img_x = data_y;

                let img_idx = (img_x + img_y * SCREEN_WIDTH) * 3;
                img[img_idx] = bit * 255;
                img[img_idx + 1] = bit * 255;
                img[img_idx + 2] = bit * 255;
            }
        }
    }

    let texture_creator = canvas.texture_creator();
    let texture = sdl2::surface::Surface::from_data(
        &mut img,
        SCREEN_WIDTH as u32,
        SCREEN_HEIGHT as u32,
        (SCREEN_WIDTH * 3) as u32,
        sdl2::pixels::PixelFormatEnum::RGB24,
    )
    .map_err(Report::msg)?
    .as_texture(&texture_creator)?;

    canvas.copy(&texture, None, None).map_err(Report::msg)
}

fn main() -> Result<()> {
    let args = Args::parse();

    let org = usize::from_str_radix(&args.org, 16)?;
    let rom =
        std::fs::read(&args.rom).wrap_err_with(|| format!("Failed to open ROM {:?}", args.rom))?;

    let mut cpu = Cpu8080::new();
    cpu.pc = org as u16;
    let mut io = IO::new(org, &rom);

    let ctx = sdl2::init().map_err(Report::msg)?;
    let video_sub = ctx.video().map_err(Report::msg)?;

    let window = video_sub
        .window("Space Invaders Emulator", 224, 256)
        .position_centered()
        .opengl()
        .build()?;

    let mut canvas = window.into_canvas().build()?;

    canvas.set_draw_color(Color::RGB(0, 0, 0));
    canvas.clear();
    canvas.present();

    let mut event_pump = ctx.event_pump().map_err(Report::msg)?;

    'main_loop: loop {
        for event in event_pump.poll_iter() {
            if let Event::Quit { .. } = event {
                break 'main_loop;
            }
        }

        for _ in 0..2 {
            cpu.raise_int(&mut io, 2);

            for _ in 0..15000 {
                cpu.step(&mut io);
            }

            if io.wrote_vram {
                draw(&io, &mut canvas)?;
                canvas.present();
                io.wrote_vram = false;
            }

            std::thread::sleep(std::time::Duration::new(0, 1_000_000_000u32 / 30));
        }
    }

    Ok(())
}
