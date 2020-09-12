extern crate anyhow;
extern crate enum_dispatch;
extern crate nom;
extern crate nom_locate;
extern crate yansi;
extern crate bitflags;
extern crate indexmap;
extern crate pretty_env_logger;
#[macro_use] extern crate log;

mod ast;
mod infer;
mod parser;
mod graph;

use parser::run_parser;
use infer::FormatAtPos;

use anyhow::{Context, Result};
use yansi::Paint;

fn main() -> Result<()> {
    try_main()
}

fn try_main() -> Result<()> {
    // TODO: write custom "pretty" logger using Paint colors and env_logger
    pretty_env_logger::init();

    if cfg!(windows) && !Paint::enable_windows_ascii() {
        Paint::disable();
    }

    let test_file = parser::File {
        prog: "
b(x) = a(\"12l3\");
a(x) = { a(1); a(x); x };
        ".to_string(),
        path: "-".to_string(),
    };

    let (module, symbols) = run_parser::<ast::Module>(&test_file)
        .context("Failed to parse file")?;

    println!("FunDefs:");
    for (path, _) in &symbols.fundefs {
        println!("\t{}", path);
    }

    let cons = module.gen_constraints(&symbols)
        .context("Failed to infer type constraints")?;

    for c in cons {
        println!("{}", c.span().format_note_at_pos(&format!("{}", c), true)?);
    }

    Ok(())
}