pub mod cpu;

#[macro_export]
#[cfg(debug_assertions)]
macro_rules! debug_print {
    ($($tts:tt)*) => {
        print!($($tts)*);
    };
}

#[macro_export]
#[cfg(debug_assertions)]
macro_rules! debug_println {
    ($($tts:tt)*) => {
        println!($($tts)*);
    };
}

#[macro_export]
#[cfg(not(debug_assertions))]
macro_rules! debug_print {
    ($($tts:tt)*) => {};
}

#[macro_export]
#[cfg(not(debug_assertions))]
macro_rules! debug_println {
    ($($tts:tt)*) => {};
}
