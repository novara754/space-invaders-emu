# Space Invaders

An emulator for the original [Space Invaders](https://en.wikipedia.org/wiki/Space_Invaders) cabinet
based on the [8080 CPU](https://en.wikipedia.org/wiki/Intel_8080).

<p align="center">
  <img
    src="https://raw.githubusercontent.com/vzwGrey/space-invaders-emu/main/screenshot.png"
    alt="Screenshot of the emulator playing Space Invaders"
  >
</p>

## Instructions

### Compiling the project

You will need to install [Rust] and [SDL2] in order to compile the emulator.
The GitHub repo for the [SDL2 Rust bindings] details the installation
process.

[Rust]: https://www.rust-lang.org/
[SDL2]: https://www.libsdl.org/index.php/
[SDL2 Rust Bindings]: https://github.com/Rust-SDL2/rust-sdl2#sdl20-development-libraries/

Once these requirements are fulfilled, the project can be compiled by running
the following command in the project's root directory:
```
$ cargo build --release
```

### Running the emulator

This emulator does not ship with the Space Invaders ROM, this will need to be
sourced separately. Typically, this ROM is distributed as a collection of
*.e, *.f, *.g and *.h files. These files will need to be concatenated as 
as follows to be used with this emulator (filenames may vary):
```
$ cat invaders.{h,g,f,e} > invaders.rom
```

Once the emulator has been compiled and the ROM file has been generated, the
emulator can be invoked as follows:
```
$ ./target/release/emu /path/to/invaders.rom
```

### Controls

Once the emulator starts, the game will go into "demo mode". To start the
actual game you need to insert a coin by pressing the <kbd>C</kbd> key. This
will start player 1's turn. Player 1 can begin their turn by pressing the
left <kbd>Ctrl</kbd> key. Once in the game, the player character can be moved
left and right with <kbd>A</kbd> and <kbd>D</kbd> respectively. Shooting can
be done with the <kbd>Space</kbd> key.

## Missing features

- Player 2 controls
- Sound
- Game configuration

## License

Licensed under the [MIT License](./LICENSE).
