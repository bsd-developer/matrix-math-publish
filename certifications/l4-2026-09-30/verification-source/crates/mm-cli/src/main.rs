//! The `mm` command-line shell (spec §9.1–§9.3).
//!
//! This binary is the I/O shell (§17.2): process control, filesystem access, and
//! subprocess orchestration live here, and nothing here can weaken a checker
//! verdict (§17.7). Exit codes are stable per §9.3.

#![forbid(unsafe_code)]
#![deny(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::todo,
    clippy::unimplemented,
    missing_docs,
    rust_2018_idioms
)]

mod cas;
mod config;
mod lean;
mod lean_omega;
mod prove;
mod replay;
mod report;
mod roundtrip;
mod search;
mod series_length;
mod verify;

use mm_core::error::CoreError;
use std::process::ExitCode;

/// Exit code for a successful run (§9.3).
const EXIT_OK: u8 = 0;
/// Exit code for an invalid command or configuration (§9.3).
const EXIT_USAGE: u8 = 2;

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let Some(command) = arguments.first().map(String::as_str) else {
        usage();
        return ExitCode::from(EXIT_USAGE);
    };
    let rest = arguments.get(1..).unwrap_or_default();

    let outcome = match command {
        "verify" => verify::run(rest),
        "omega-min" => verify::omega_min(rest),
        "to-symmetric" => verify::to_symmetric(rest),
        "prove" => prove::run(rest),
        "search" => search::run(rest),
        "series-length" => series_length::run(rest),
        "replay" => replay::run(rest),
        "cas-put" => cas::put(rest),
        "cas-get" => cas::get(rest),
        "report" => report::run(rest),
        "verify-release" => report::verify_release(rest),
        "doctor" => doctor(rest),
        "--help" | "-h" | "help" => {
            usage();
            return ExitCode::from(EXIT_OK);
        }
        "--version" | "-V" => {
            println!("mm {}", env!("CARGO_PKG_VERSION"));
            return ExitCode::from(EXIT_OK);
        }
        other => {
            eprintln!("mm: unknown command {other:?}");
            usage();
            return ExitCode::from(EXIT_USAGE);
        }
    };

    match outcome {
        Ok(code) => ExitCode::from(code),
        Err(error) => {
            report_error(&error);
            ExitCode::from(u8::try_from(error.exit_code()).unwrap_or(EXIT_USAGE))
        }
    }
}

fn report_error(error: &CoreError) {
    eprintln!("REJECTED");
    eprintln!("  code       {}", error.code());
    if let Some(equation) = error.equation_id() {
        eprintln!("  equation   {equation}");
    }
    eprintln!("  location   {}", error.location());
    eprintln!("  detail     {}", error.message());
    for value in error.values() {
        eprintln!("  value      {value}");
    }
}

fn usage() {
    eprintln!(
        "\
matrix-math command line (spec §9.3)

  mm verify <file> [--profile ck|cn] [--json]
  mm prove  <file> [--profile ck|cn] [--json]
  mm omega-min <omega-certificate>
  mm series-length <numerator> <denominator> <precision>
  mm search --config <toml> [--out <file>]
  mm replay <run-dir> [--level witness|bitwise|statistical]
  mm cas-put <file>
  mm cas-get <sha256> [--out <file>]
  mm report <file> [--profile ck|cn]
  mm verify-release <manifest.json>
  mm doctor [--json]

Exit codes: 0 verified, 2 invalid command, 3 certificate rejected,
4 unsupported instance, 5 resource limit, 6 implementation disagreement."
    );
}

fn doctor(arguments: &[String]) -> Result<u8, CoreError> {
    let json = arguments.iter().any(|argument| argument == "--json");
    let ledger = mm_registry::TcbLedger::from_environment("none")?;
    if json {
        println!("{}", ledger.to_canonical_json());
    } else {
        println!("matrix-math doctor");
        for (component, version) in ledger.entries() {
            println!("  {component:<22} {version}");
        }
    }
    Ok(EXIT_OK)
}
