//! Run configuration (spec §9.5, §13.7).
//!
//! Long-running commands accept TOML only. Unknown fields are **rejected**, and
//! CLI flags may select a config or an operational resume mode but must never
//! silently override a scientific parameter in the file (§9.5).
//!
//! The parsed, normalized config is canonicalized and hashed before a run
//! starts, so the run record identifies exactly the parameters that ran.
//!
//! The reader implements the strict TOML subset the schema uses — bare keys,
//! integers, booleans, basic strings, and one level of table — rather than
//! pulling in a general TOML parser. That keeps rejection behaviour explicit and
//! the dependency surface small; anything outside the subset is a structured
//! error rather than a best-effort interpretation.

use mm_core::codes::ErrorCode;
use mm_core::error::{CoreError, CoreResult, push_json_string};
use mm_core::hex::{decode_hex32, encode_hex};
use std::collections::BTreeMap;

/// The config schema this build accepts.
pub const CONFIG_SCHEMA: &str = "matrix-math-run-config/1";

/// One parsed scalar value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    /// A basic string.
    Str(String),
    /// A non-negative integer.
    Int(u64),
    /// A boolean.
    Bool(bool),
}

impl Value {
    fn type_name(&self) -> &'static str {
        match self {
            Self::Str(_) => "string",
            Self::Int(_) => "integer",
            Self::Bool(_) => "boolean",
        }
    }
}

/// A parsed configuration document: `section.key -> value`, both sorted.
#[derive(Clone, Debug, Default)]
pub struct Document {
    entries: BTreeMap<String, Value>,
}

fn bad(message: impl Into<String>, line: usize) -> CoreError {
    CoreError::new(ErrorCode::BadConfig, message)
        .equation("§9.5")
        .value(format!("line {line}"))
}

impl Document {
    /// Parse the supported TOML subset.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadConfig`] for anything outside the subset,
    /// including a duplicate key.
    pub fn parse(text: &str) -> CoreResult<Self> {
        let mut entries: BTreeMap<String, Value> = BTreeMap::new();
        let mut section = String::new();
        for (index, raw) in text.lines().enumerate() {
            let line_number = index + 1;
            let line = strip_comment(raw).trim();
            if line.is_empty() {
                continue;
            }
            if let Some(rest) = line.strip_prefix('[') {
                let name = rest
                    .strip_suffix(']')
                    .ok_or_else(|| bad("unterminated table header", line_number))?
                    .trim();
                if name.is_empty() || !name.chars().all(is_key_char) {
                    return Err(bad("table names use bare keys only", line_number));
                }
                section = name.to_owned();
                continue;
            }
            let (key, value) = line
                .split_once('=')
                .ok_or_else(|| bad("expected key = value", line_number))?;
            let key = key.trim();
            if key.is_empty() || !key.chars().all(is_key_char) {
                return Err(bad("keys must be bare", line_number));
            }
            let qualified = if section.is_empty() {
                key.to_owned()
            } else {
                format!("{section}.{key}")
            };
            let parsed = parse_value(value.trim(), line_number)?;
            if entries.insert(qualified.clone(), parsed).is_some() {
                return Err(bad(format!("duplicate key {qualified}"), line_number));
            }
        }
        Ok(Self { entries })
    }

    /// Look up a key.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&Value> {
        self.entries.get(key)
    }

    /// All keys present, sorted.
    #[must_use]
    pub fn keys(&self) -> Vec<&str> {
        self.entries.keys().map(String::as_str).collect()
    }

    fn require(&self, key: &str) -> CoreResult<&Value> {
        self.entries.get(key).ok_or_else(|| {
            CoreError::new(ErrorCode::BadConfig, "a required config field is absent")
                .equation("§9.5")
                .value(key)
        })
    }

    fn string(&self, key: &str) -> CoreResult<&str> {
        match self.require(key)? {
            Value::Str(value) => Ok(value),
            other => Err(type_error(key, "string", other)),
        }
    }

    fn integer(&self, key: &str) -> CoreResult<u64> {
        match self.require(key)? {
            Value::Int(value) => Ok(*value),
            other => Err(type_error(key, "integer", other)),
        }
    }

    fn boolean(&self, key: &str) -> CoreResult<bool> {
        match self.require(key)? {
            Value::Bool(value) => Ok(*value),
            other => Err(type_error(key, "boolean", other)),
        }
    }

    /// Render the normalized document as canonical JSON with sorted keys (§9.5).
    #[must_use]
    pub fn to_canonical_json(&self) -> String {
        let mut out = String::from("{");
        for (index, (key, value)) in self.entries.iter().enumerate() {
            if index > 0 {
                out.push(',');
            }
            push_json_string(&mut out, key);
            out.push(':');
            match value {
                Value::Str(text) => push_json_string(&mut out, text),
                Value::Int(number) => out.push_str(&number.to_string()),
                Value::Bool(flag) => out.push_str(if *flag { "true" } else { "false" }),
            }
        }
        out.push('}');
        out
    }
}

fn type_error(key: &str, expected: &str, found: &Value) -> CoreError {
    CoreError::new(ErrorCode::BadConfig, "a config field has the wrong type")
        .equation("§9.5")
        .value(key)
        .value(format!("expected {expected}, found {}", found.type_name()))
}

const fn is_key_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_' || ch == '-'
}

fn strip_comment(line: &str) -> &str {
    let mut in_string = false;
    for (index, ch) in line.char_indices() {
        match ch {
            '"' => in_string = !in_string,
            '#' if !in_string => return line.get(..index).unwrap_or(""),
            _ => {}
        }
    }
    line
}

fn parse_value(text: &str, line: usize) -> CoreResult<Value> {
    if text == "true" {
        return Ok(Value::Bool(true));
    }
    if text == "false" {
        return Ok(Value::Bool(false));
    }
    if let Some(rest) = text.strip_prefix('"') {
        let body = rest
            .strip_suffix('"')
            .ok_or_else(|| bad("unterminated string", line))?;
        if body.contains('\\') {
            return Err(bad(
                "string escapes are not part of the config subset",
                line,
            ));
        }
        return Ok(Value::Str(body.to_owned()));
    }
    let digits: String = text.chars().filter(|ch| *ch != '_').collect();
    if !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return digits
            .parse::<u64>()
            .map(Value::Int)
            .map_err(|_| bad("integer out of range", line));
    }
    Err(bad(
        "unsupported value; use a string, integer, or boolean",
        line,
    ))
}

/// A validated Track B search configuration (§9.5).
#[derive(Clone, Debug)]
pub struct SearchConfig {
    /// The exact algorithm name.
    pub algorithm: String,
    /// The algorithm version, recorded so a change cannot be silent.
    pub algorithm_version: String,
    /// The hardware profile this run targets.
    pub hardware_profile: String,
    /// The experiment target, e.g. `"T4-f2-47"`.
    pub target: String,
    /// Matrix dimensions.
    pub n: u16,
    /// Matrix dimensions.
    pub m: u16,
    /// Matrix dimensions.
    pub p: u16,
    /// The term count that counts as success.
    pub target_terms: usize,
    /// The 256-bit master seed.
    pub master_seed: [u8; 32],
    /// Number of independent workers (§10.8: one per performance core).
    pub workers: u32,
    /// The deterministic evaluation budget per worker.
    pub step_budget: u64,
    /// Optional wall-clock safety limit in seconds (0 disables).
    pub wall_clock_limit_seconds: u64,
    /// Steps between checkpoints.
    pub checkpoint_interval: u64,
    /// Steps without improvement before a deterministic restart.
    pub restart_interval: u64,
    /// Process memory limit in mebibytes.
    pub memory_limit_mib: u64,
    /// Whether plus transitions are enabled (§10.5 disables them by default).
    pub allow_plus: bool,
    /// Where a deterministic restart resumes from: `"naive"` or `"best"`.
    pub restart_policy: String,
    /// Steps without improvement before a plus transition (§10.5).
    pub plus_interval: u64,
    /// The largest term count a plus transition may grow the state to.
    pub max_terms: usize,
    /// Whether to verify the tensor invariant after every move (§12.5).
    pub verify_every_move: bool,
    /// Steps between full reconstruction checks (0 disables).
    pub full_check_interval: u64,
    /// The canonical digest of the normalized config (§9.5, §13.7).
    pub digest: String,
}

/// Every key the search config schema defines. Anything else is rejected (§9.5).
const SEARCH_KEYS: [&str; 21] = [
    "schema",
    "experiment.kind",
    "experiment.target",
    "experiment.hardware_profile",
    "algorithm.name",
    "algorithm.version",
    "algorithm.allow_plus",
    "algorithm.restart_interval",
    "algorithm.restart_policy",
    "algorithm.plus_interval",
    "algorithm.max_terms",
    "instance.n",
    "instance.m",
    "instance.p",
    "instance.target_terms",
    "run.master_seed",
    "run.workers",
    "run.step_budget",
    "run.wall_clock_limit_seconds",
    "run.checkpoint_interval",
    "run.memory_limit_mib",
];

/// Optional keys that may be absent.
const SEARCH_OPTIONAL: [&str; 2] = ["debug.verify_every_move", "debug.full_check_interval"];

impl SearchConfig {
    /// Parse and validate a search configuration.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::BadConfig`] for a missing, misspelled, or wrongly
    /// typed field.
    pub fn parse(text: &str) -> CoreResult<Self> {
        let document = Document::parse(text)?;
        for key in document.keys() {
            if !SEARCH_KEYS.contains(&key) && !SEARCH_OPTIONAL.contains(&key) {
                return Err(CoreError::new(
                    ErrorCode::BadConfig,
                    "unknown configuration field; §9.5 rejects rather than ignores",
                )
                .equation("§9.5")
                .value(key));
            }
        }
        let schema = document.string("schema")?;
        if schema != CONFIG_SCHEMA {
            return Err(
                CoreError::new(ErrorCode::BadConfig, "unsupported config schema")
                    .equation("§9.5")
                    .value(schema),
            );
        }
        let kind = document.string("experiment.kind")?;
        if kind != "search" {
            return Err(CoreError::new(
                ErrorCode::BadConfig,
                "this command runs search experiments",
            )
            .equation("§9.5")
            .value(kind));
        }
        let seed_text = document.string("run.master_seed")?;
        let master_seed = decode_hex32(seed_text)?;

        let narrow = |key: &str| -> CoreResult<u16> {
            let value = document.integer(key)?;
            u16::try_from(value).map_err(|_| {
                CoreError::new(ErrorCode::UnsupportedInstance, "dimension out of range")
                    .equation("§0.2")
                    .value(key)
            })
        };

        let config = Self {
            algorithm: document.string("algorithm.name")?.to_owned(),
            algorithm_version: document.string("algorithm.version")?.to_owned(),
            hardware_profile: document.string("experiment.hardware_profile")?.to_owned(),
            target: document.string("experiment.target")?.to_owned(),
            n: narrow("instance.n")?,
            m: narrow("instance.m")?,
            p: narrow("instance.p")?,
            target_terms: usize::try_from(document.integer("instance.target_terms")?).map_err(
                |_| {
                    CoreError::new(ErrorCode::BadConfig, "target_terms out of range")
                        .equation("§9.5")
                },
            )?,
            master_seed,
            workers: u32::try_from(document.integer("run.workers")?).map_err(|_| {
                CoreError::new(ErrorCode::BadConfig, "workers out of range").equation("§9.5")
            })?,
            step_budget: document.integer("run.step_budget")?,
            wall_clock_limit_seconds: document.integer("run.wall_clock_limit_seconds")?,
            checkpoint_interval: document.integer("run.checkpoint_interval")?,
            restart_interval: document.integer("algorithm.restart_interval")?,
            memory_limit_mib: document.integer("run.memory_limit_mib")?,
            allow_plus: document.boolean("algorithm.allow_plus")?,
            restart_policy: document.string("algorithm.restart_policy")?.to_owned(),
            plus_interval: document.integer("algorithm.plus_interval")?,
            max_terms: usize::try_from(document.integer("algorithm.max_terms")?).map_err(|_| {
                CoreError::new(ErrorCode::BadConfig, "max_terms out of range").equation("§9.5")
            })?,
            verify_every_move: document
                .get("debug.verify_every_move")
                .is_some_and(|value| *value == Value::Bool(true)),
            full_check_interval: match document.get("debug.full_check_interval") {
                Some(Value::Int(value)) => *value,
                _ => 0,
            },
            digest: encode_hex(&mm_core::sha256(document.to_canonical_json().as_bytes())),
        };

        if config.workers == 0 {
            return Err(
                CoreError::new(ErrorCode::BadConfig, "a run needs at least one worker")
                    .equation("§9.5"),
            );
        }
        if config.step_budget == 0 {
            return Err(CoreError::new(
                ErrorCode::BadConfig,
                "a run needs a nonzero evaluation budget; §10.8 makes it the stopping rule",
            )
            .equation("§10.8"));
        }
        if !matches!(config.restart_policy.as_str(), "naive" | "best") {
            return Err(CoreError::new(
                ErrorCode::BadConfig,
                "restart_policy must be \"naive\" or \"best\"",
            )
            .equation("§10.8")
            .value(config.restart_policy.clone()));
        }
        if config.allow_plus && config.plus_interval == 0 {
            return Err(CoreError::new(
                ErrorCode::BadConfig,
                "enabling plus transitions requires a nonzero plus_interval",
            )
            .equation("§10.5"));
        }
        if config.allow_plus && config.max_terms <= config.target_terms {
            return Err(CoreError::new(
                ErrorCode::BadConfig,
                "max_terms must exceed target_terms, or a plus transition can never run",
            )
            .equation("§10.5"));
        }
        Ok(config)
    }
}
