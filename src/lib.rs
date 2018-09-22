#[macro_use]
extern crate nom;

pub mod parser;

#[derive(Debug, PartialEq)]
pub struct Color {
    pub red: u8,
    pub green: u8,
    pub blue: u8,
}

fn from_hex(input: &str) -> Result<u8, std::num::ParseIntError> {
    u8::from_str_radix(input, 16)
}

fn is_hex_digit(c: char) -> bool {
    let c = c as u8;
    (c >= 0x30 && c <= 0x39) || (c >= 0x41 && c <= 0x46) || (c >= 0x61 && c <= 0x66)
}

named!(hex_primary<&str, u8>,
       map_res!(take_while_m_n!(2, 2, is_hex_digit), from_hex)
);

named!(pub hex_color<&str, Color>,
       do_parse!(
           tag!("#")   >>
               red:   hex_primary >>
               green: hex_primary >>
               blue:  hex_primary >>
               (Color { red, green, blue })
       )
);
