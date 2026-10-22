#!/usr/bin/env bash
# Print the WHIR parameters the pinned leanVM derives for every admissible witness size and rate:
# per level, the Johnson slack `eta` as the bits of its IEEE double and the query count
# (`pcs::whir_config::WhirSecurityConfig::derive_config_with_log_inv_rate`,
# crates/pcs/src/whir_config.rs at a386121f84292f6fa663aaa3e570c15bc0240ea2). Lines read
# `R mu level eta_bits queries`, with `mu` the packed log-size (the Rust's `m` less
# `LOG_PACKING`). `scripts/whir-mca-budget.py --rust-eta FILE` compares its reproduction with them.
#
# Usage: scripts/dump-whir-eta-rust.sh <path to a leanVM checkout at the pin>
set -euo pipefail

pin="a386121f84292f6fa663aaa3e570c15bc0240ea2"
checkout="$(cd "${1:?usage: $0 <leanVM checkout>}" && pwd)"
head="$(git -C "$checkout" rev-parse HEAD)"
if [[ "$head" != "$pin" ]]; then
  echo "leanVM checkout is at $head, not the pin $pin" >&2
  exit 1
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/src"
cp "$checkout/Cargo.lock" "$work/Cargo.lock"

cat > "$work/Cargo.toml" <<EOF
[package]
name = "dump-whir-eta"
version = "0.0.0"
edition = "2024"

[dependencies]
pcs = { path = "$checkout/crates/pcs" }
EOF

cat > "$work/src/main.rs" <<'EOF'
use pcs::whir_config::{WhirSecurityConfig, MAX_LOG_INV_RATE, MIN_LOG_INV_RATE};
use pcs::LOG_PACKING;

fn main() {
    for r in MIN_LOG_INV_RATE..=MAX_LOG_INV_RATE {
        for mu in 15..=28usize {
            let cfg = WhirSecurityConfig::derive_config_with_log_inv_rate(mu + LOG_PACKING, r).unwrap();
            for (i, level) in cfg.levels.iter().enumerate() {
                println!("{r} {mu} {i} {} {}", level.eta.to_bits(), level.queries);
            }
        }
    }
}
EOF

cargo run --quiet --release --manifest-path "$work/Cargo.toml" --target-dir "$checkout/target"
