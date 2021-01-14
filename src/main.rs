extern crate anyhow;
extern crate enum_dispatch;
extern crate nom;
extern crate nom_locate;
extern crate yansi;
extern crate bitflags;
extern crate indexmap;
extern crate vecshard;
extern crate itertools;
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
struct Foo {index :: Int};
struct First {index :: Int, other :: Bool};
struct Second(Int, ());

infix right 2 +;
infix left 1 -;

`+`(a, b) = a;
`-`(a, b) = b;

id(x) = if
    | True: Second(x - 1, {})
    | c(x): Second(123, {})
    | Second(9, {});

c(x) = False;
        ".to_string(),
        path: "-".to_string(),
    };

    let (module, symbols, tvs) = run_parser::<ast::Module>(&test_file)
        .context("Failed to parse file")?;

    println!("FunDefs:");
    for (path, _) in &symbols.fundefs {
        println!("\t{}", path);
    }

    let types = module
        .gen_constraints(&symbols, tvs)
        .context("Failed to infer type constraints")?;

    for (_nodeid, (ty, span)) in types {
        println!("{}", span.format_note_at_pos(&format!("{}", ty), true)?);
    }

    Ok(())
}
