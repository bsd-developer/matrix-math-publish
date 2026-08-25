mm := "./target/release/mm"

# toolchain and locked-source health check
doctor:
    ./scripts/doctor

# Rust checker and Lean project
build:
    cargo build --release -p mm-cli
    cd lean && lake build

# independent exact verification of a certificate
verify FILE *ARGS:
    cargo build --release -p mm-cli
    {{mm}} verify {{FILE}} {{ARGS}}

# generate and check the certificate-specific Lean theorem
prove FILE PROFILE="cn":
    cargo build --release -p mm-cli
    {{mm}} prove {{FILE}} --profile {{PROFILE}}
