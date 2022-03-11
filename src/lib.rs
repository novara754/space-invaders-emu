#![allow(clippy::unused_unit)]
#![feature(bigint_helper_methods)]

pub mod cpu;

use wasm_bindgen::prelude::*;

use cpu::{Address, Byte, Cpu8080, IOManager};
use web_sys::{CanvasRenderingContext2d, ImageData};

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    pub fn log(s: &str);
}

#[macro_export]
macro_rules! console_log {
    // Note that this is using the `log` function imported above during
    // `bare_bones`
    ($($t:tt)*) => ($crate::log(&format_args!($($t)*).to_string()))
}

#[macro_export]
macro_rules! debug_print {
    ($($tts:tt)*) => {
        //  $crate::console_log!($($tts)*);
    };
}

#[macro_export]
macro_rules! debug_println {
    ($($tts:tt)*) => {
        //  $crate::console_log!($($tts)*);
    };
}

const SCREEN_WIDTH: usize = 224;
const SCREEN_HEIGHT: usize = 256;

#[wasm_bindgen]
pub fn key_start() -> u8 {
    1 << 2
}
#[wasm_bindgen]
pub fn key_left() -> u8 {
    1 << 5
}
#[wasm_bindgen]
pub fn key_right() -> u8 {
    1 << 7
}
#[wasm_bindgen]
pub fn key_shoot() -> u8 {
    1 << 4
}

#[wasm_bindgen]
pub struct IO {
    rom: Vec<Byte>,
    ram: Vec<Byte>,
    vram: Vec<Byte>,
    wrote_vram: bool,

    shift_reg_hi: u8,
    shift_reg_lo: u8,
    shift_offset: u8,

    buttons1: u8,
    buttons2: u8,
}

impl IO {
    pub fn new(rom: &[Byte]) -> Self {
        let rom = Vec::from(rom);
        let ram = vec![0; 0x23FF - 0x2000 + 1];
        let vram = vec![0; 0x3FFF - 0x2400 + 1];
        Self {
            rom,
            ram,
            vram,
            wrote_vram: false,

            shift_reg_hi: 0,
            shift_reg_lo: 0,
            shift_offset: 0,

            buttons1: 0,
            buttons2: 0,
        }
    }

    pub fn key_down(&mut self, key: u8) {
        console_log!("key down: {}", key);
        self.buttons1 |= key;
    }

    pub fn key_up(&mut self, key: u8) {
        console_log!("key up: {}", key);
        self.buttons1 &= !key;
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
                self.wrote_vram = true
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

#[wasm_bindgen]
pub struct Emulator {
    cpu: Cpu8080,
    io: IO,
}

#[wasm_bindgen]
impl Emulator {
    #[allow(clippy::new_without_default)]
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        let rom = include_bytes!("../roms/invaders.rom");

        let cpu = Cpu8080::new();
        let io = IO::new(rom);

        Emulator { cpu, io }
    }

    #[wasm_bindgen]
    pub fn step(&mut self) {
        self.cpu.step(&mut self.io);
    }

    #[wasm_bindgen]
    pub fn raise_int(&mut self, int_num: u16) {
        self.cpu.raise_int(&mut self.io, int_num);
    }

    #[wasm_bindgen]
    pub fn draw(&self, ctx: &CanvasRenderingContext2d) {
        if self.io.wrote_vram {
            let mut img = [0u8; SCREEN_HEIGHT * SCREEN_WIDTH * 4];

            let bytes_per_row = SCREEN_HEIGHT / 8;

            for data_y in 0..SCREEN_WIDTH {
                for data_x in 0..bytes_per_row {
                    let byte_idx = data_y * bytes_per_row + data_x;
                    let byte = self.io.vram[byte_idx];

                    for bit_idx in 0..8 {
                        let bit = (byte >> bit_idx) & 1;

                        let img_y = SCREEN_HEIGHT - 1 - (data_x * 8 + bit_idx);
                        let img_x = data_y;

                        let img_idx = (img_x + img_y * SCREEN_WIDTH) * 4;
                        img[img_idx] = bit * 255;
                        img[img_idx + 1] = bit * 255;
                        img[img_idx + 2] = bit * 255;
                        img[img_idx + 3] = 255;
                    }
                }
            }

            // for (byte_idx, byte) in self.io.vram.iter().enumerate() {
            //     for bit_idx in 0..8 {
            //         let bit = (byte >> bit_idx) & 1;
            //         img[byte_idx * 4] = bit * 255;
            //         img[byte_idx * 4 + 1] = bit * 255;
            //         img[byte_idx * 4 + 2] = bit * 255;
            //         img[byte_idx * 4 + 3] = 255;
            //     }
            // }

            let img_data = ImageData::new_with_u8_clamped_array_and_sh(
                wasm_bindgen::Clamped(&img),
                SCREEN_WIDTH as u32,
                SCREEN_HEIGHT as u32,
            )
            .unwrap();
            ctx.put_image_data(&img_data, 0.0, 0.0).unwrap();
        }
    }

    #[wasm_bindgen]
    pub fn key_down(&mut self, key: u8) {
        self.io.key_down(key);
    }

    #[wasm_bindgen]
    pub fn key_up(&mut self, key: u8) {
        self.io.key_up(key);
    }
}

#[wasm_bindgen(start)]
pub fn start() {
    std::panic::set_hook(Box::new(console_error_panic_hook::hook));
}
