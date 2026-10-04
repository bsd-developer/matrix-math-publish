//! The external trusted computing base ledger (spec §3.3).
//!
//! Every published result must identify, by version and hash where practical,
//! the software actually trusted for the computation. The ledger is deliberately
//! separate from the **logical axiom** list: Lean kernel soundness is a
//! metatheoretic assumption and belongs here, not in `#print axioms` output
//! (§3.2).

use mm_core::error::{CoreResult, push_json_string};
use std::collections::BTreeMap;

/// A machine-readable TCB ledger.
#[derive(Clone, Debug, Default)]
pub struct TcbLedger {
    entries: BTreeMap<String, String>,
}

impl TcbLedger {
    /// An empty ledger.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record one component and its exact version or hash.
    pub fn record(&mut self, component: impl Into<String>, version: impl Into<String>) {
        self.entries.insert(component.into(), version.into());
    }

    /// The recorded entries, sorted by component name.
    #[must_use]
    pub fn entries(&self) -> &BTreeMap<String, String> {
        &self.entries
    }

    /// Render the ledger as canonical JSON with sorted keys.
    #[must_use]
    pub fn to_canonical_json(&self) -> String {
        let mut out = String::from("{\"components\":{");
        for (index, (component, version)) in self.entries.iter().enumerate() {
            if index > 0 {
                out.push(',');
            }
            push_json_string(&mut out, component);
            out.push(':');
            push_json_string(&mut out, version);
        }
        out.push_str("},\"note\":");
        push_json_string(
            &mut out,
            "Lean kernel soundness is a metatheoretic assumption recorded here, \
             not a Lean axiom (spec §3.2).",
        );
        out.push_str(",\"schema\":\"matrix-math-tcb-ledger/1\"}");
        out
    }

    /// Collect the ambient toolchain facts a published result must record (§3.3).
    ///
    /// Values that cannot be determined are recorded as `"unavailable"` rather
    /// than omitted, so a reader can tell the difference between "not applicable"
    /// and "not captured".
    ///
    /// # Errors
    ///
    /// Never fails; the signature is `Result` so callers can chain it.
    pub fn from_environment(profile: &str) -> CoreResult<Self> {
        let mut ledger = Self::new();
        ledger.record("certification_profile", profile);
        ledger.record("os", std::env::consts::OS);
        ledger.record("arch", std::env::consts::ARCH);
        ledger.record("spec_version", mm_core::SPEC_VERSION);
        ledger.record("rust_checker", env!("CARGO_PKG_VERSION"));
        for (component, program, args) in [
            ("lean", "lean", ["--version"]),
            ("lake", "lake", ["--version"]),
        ] {
            let value = std::process::Command::new(program)
                .args(args)
                .output()
                .ok()
                .filter(|output| output.status.success())
                .map(|output| {
                    String::from_utf8_lossy(&output.stdout)
                        .lines()
                        .next()
                        .unwrap_or_default()
                        .trim()
                        .to_owned()
                })
                .unwrap_or_else(|| String::from("unavailable"));
            ledger.record(component, value);
        }
        Ok(ledger)
    }
}
