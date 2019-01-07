use std::io;

use ansi_term::Color;
use linefeed::{Interface, ReadResult, Terminal};

use crate::evaluator;
use crate::printer;

static HISTORY_FILE: &str = "ubiquity.history";

fn configure_reader<T: Terminal>(reader: &Interface<T>) -> io::Result<()> {
    let mut reader = reader.lock_reader();
    reader.set_blink_matching_paren(true);

    let style = Color::Purple.bold();
    let text = "ubiquity=> ";

    reader.set_prompt(&format!(
        "\x01{prefix}\x02{text}\x01{suffix}\x02",
        prefix = style.prefix(),
        text = text,
        suffix = style.suffix()
    ))
}

pub fn run() -> io::Result<()> {
    let reader = Interface::new("ubiquity")?;
    configure_reader(&reader)?;

    if let Err(e) = reader.load_history(HISTORY_FILE) {
        if e.kind() == io::ErrorKind::NotFound {
            println!(
                "History file {} doesn't exist, not loading history.",
                HISTORY_FILE
            );
        } else {
            eprintln!("Could not load history file {}: {}", HISTORY_FILE, e);
        }
    }

    loop {
        match reader.read_line()? {
            ReadResult::Input(input) => {
                if input.len() == 0 {
                    continue;
                }
                reader.add_history_unique(input.clone());
                rep(&input)?
            }
            ReadResult::Eof => {
                print!("^D");
                break;
            }
            ReadResult::Signal(signal) => {
                println!("signal: {:?}", signal);
                break;
            }
        }
    }

    if let Err(e) = reader.save_history(HISTORY_FILE) {
        eprintln!("Could not save history file {}: {}", HISTORY_FILE, e);
    }

    Ok(())
}

fn rep(input: &str) -> io::Result<()> {
    let results = evaluator::eval(input);
    printer::println_to(io::stdout(), results.as_slice())
}
