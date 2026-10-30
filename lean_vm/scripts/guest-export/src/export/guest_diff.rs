//! Real aggregations for the Lean differential check of the guest (`lean_vm/cli/GuestDiff.lean`): per case,
//! the node's statement, its seed and witness (`LeanVM.Node.NodeWitness`: every child's statement, fresh claim and
//! raw proof, a holder per claim, the batching's hints), the streams `aggregate` installed, the public input and the
//! run's memory size, as whitespace-separated tokens. Ported from the BLAKE2s-era `guest_diff`: Flock's claims are
//! gone (a deferred and a fresh claim are a point and a value), and the installed streams are read through
//! `aggregation.rs`'s test-only `FORGE` hook, which hands this module the node's `Hints` before they are installed.
//! `LEANVM_GUEST_DIFF=<dir> cargo test --release --manifest-path scripts/guest-export/Cargo.toml --lib guest_diff -- --ignored`
//! writes `<dir>/<case>.txt`.
//!
//! The tokens: a field element is its three limbs in hex, a `K` word one hex token, a byte string one hex token, a
//! list its length then its items; a section starts with its name, which the reader checks.

use super::*;
use crate::signers_cache::{get_lean_sphincs_signers, get_signers, message};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::fmt::Write as _;

thread_local! {
    /// The streams of the last node this thread aggregated, as the `FORGE` hook saw them.
    static INSTALLED: std::cell::RefCell<Vec<(String, Vec<Vec<F192>>)>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Have the next node this thread aggregates record its streams in `INSTALLED`, unchanged.
fn capture_next() {
    FORGE.with(|forge| {
        *forge.borrow_mut() = Some(Box::new(|hints: &mut Hints| {
            INSTALLED.with(|i| *i.borrow_mut() = hints.0.clone());
        }));
    });
}

struct Out(String);

impl Out {
    fn tag(&mut self, tag: &str) {
        write!(self.0, "\n{tag} ").unwrap();
    }

    fn n(&mut self, n: usize) {
        write!(self.0, "{n} ").unwrap();
    }

    fn e(&mut self, x: F192) {
        write!(self.0, "{:x} {:x} {:x} ", x.c0, x.c1, x.c2).unwrap();
    }

    fn es(&mut self, xs: &[F192]) {
        self.n(xs.len());
        for &x in xs {
            self.e(x);
        }
    }

    fn bytes(&mut self, bytes: &[u8]) {
        for b in bytes {
            write!(self.0, "{b:02x}").unwrap();
        }
        self.0.push(' ');
    }

    fn digests<const N: usize>(&mut self, digests: &[[u8; N]]) {
        self.n(digests.len());
        for d in digests {
            self.bytes(d);
        }
    }

    fn deferred(&mut self, c: &DeferredClaim) {
        self.tag("defer");
        self.es(&c.bytecode_point);
        self.e(c.bytecode_value);
    }

    /// `NodeStatement`: the claims, the DA digest (`da_digest`), and the deferred claim.
    fn statement(&mut self, p: &EthereumProof) {
        self.tag("xmss");
        self.n(p.xmss_signers.len());
        for (pk, m) in &p.xmss_signers {
            self.bytes(&pk.flatten());
            self.bytes(m);
        }
        self.tag("sphincs");
        self.n(p.lean_sphincs_signers.len());
        for (pk, m) in &p.lean_sphincs_signers {
            self.bytes(&pk.flatten());
            self.bytes(m);
        }
        self.tag("da");
        self.bytes(&da_digest(p.da_root));
        self.deferred(&p.defer);
    }

    fn xmss_signature(&mut self, sig: &LeanXmssSignature) {
        self.n(sig.leaf_index as usize);
        for layer in [&sig.bottom, &sig.top] {
            self.bytes(&layer.randomizer);
            self.digests(&layer.chain_values);
            self.digests(&layer.path);
        }
    }

    fn sphincs_signature(&mut self, sig: &LeanSphincsSignature) {
        self.bytes(&sig.randomizer);
        for tree in &sig.forest {
            for subtree in &tree.subtrees {
                self.digests(&subtree.values);
                self.digests(&subtree.path);
            }
            self.digests(&tree.path);
        }
        self.n(sig.counter as usize);
        self.digests(&sig.wots);
        self.digests(&sig.path);
    }
}

/// Where a claim is held: its raw witness, else the first child that makes it.
fn holder<K: PartialEq>(claim: &K, raw: Option<impl FnOnce(&mut Out)>, children: &[&[K]], out: &mut Out) {
    match raw {
        Some(write) => {
            out.0.push_str("direct ");
            write(out);
        }
        None => {
            let i = children
                .iter()
                .position(|c| c.contains(claim))
                .expect("a claim is held");
            write!(out.0, "child {i} ").unwrap();
        }
    }
}

/// Aggregate, and write the case: the statement, the witness, the installed streams.
fn export(
    name: &str,
    children: Vec<EthereumProof>,
    raw_xmss: Vec<(LeanXmssPublicKey, lean_xmss::Message, LeanXmssSignature)>,
    raw_sphincs: Vec<(LeanSphincsPublicKey, lean_sphincs::Message, LeanSphincsSignature)>,
    blobs: &[u64],
) -> EthereumProof {
    capture_next();
    let node = aggregate(
        &children,
        raw_xmss.clone(),
        raw_sphincs.clone(),
        blobs,
        None,
        LOG_INV_RATE,
    )
    .expect("node aggregates");
    node.verify().expect("node verifies");
    let streams = INSTALLED.with(|i| i.take());
    let stream = |name: &str| streams.iter().find(|(n, _)| n == name).map(|(_, e)| e.as_slice());

    let mut out = Out(format!("leanvm-guest-diff 2\ncase {name}"));
    out.tag("seed");
    let seed = leanvm_core::cpu::fs_seed(unified_guest());
    out.bytes(&cell_bytes(seed));
    out.tag("log_memory");
    out.n(node.proof.stream[0].c0 as usize);
    out.tag("public_input");
    out.es(&node.statement(da_digest(node.da_root)));
    out.tag("statement");
    out.statement(&node);

    out.tag("children");
    out.n(children.len());
    let bytecode = scalar_bytecode();
    for child in &children {
        out.tag("child");
        out.statement(child);
        let pi = child.statement(da_digest(child.da_root));
        let summary = verifier::replay_unchecked(bytecode, &public_input_bytes(&pi), &scalar_proof(&child.proof))
            .expect("the child replays");
        let openings: Vec<(Vec<u64>, Vec<[u8; 32]>)> = summary
            .merkle_paths
            .iter()
            .map(|path| (path.leaf.iter().map(|w| w.0).collect(), path.siblings.clone()))
            .collect();
        let (_, fresh) = gen_verify(unified_guest(), pi, &child.proof.stream, summary).expect("the child fits");
        out.tag("fresh");
        let point: Vec<F192> = fresh.bytecode_point.clone();
        out.es(&point);
        out.e(fresh.bytecode_value);
        out.tag("proof");
        out.es(&child.proof.stream);
        out.n(openings.len());
        for (leaf, siblings) in &openings {
            out.n(leaf.len());
            for w in leaf {
                write!(out.0, "{w:x} ").unwrap();
            }
            out.digests(siblings);
        }
    }

    let xmss_children: Vec<&[LeanXmssClaim]> = children.iter().map(|c| c.xmss_signers.as_slice()).collect();
    out.tag("holders_xmss");
    out.n(node.xmss_signers.len());
    for claim in &node.xmss_signers {
        let raw = raw_xmss.iter().find(|(pk, m, _)| (*pk, *m) == *claim);
        holder(
            claim,
            raw.map(|(_, _, sig)| |out: &mut Out| out.xmss_signature(sig)),
            &xmss_children,
            &mut out,
        );
    }
    let sphincs_children: Vec<&[LeanSphincsClaim]> =
        children.iter().map(|c| c.lean_sphincs_signers.as_slice()).collect();
    out.tag("holders_sphincs");
    out.n(node.lean_sphincs_signers.len());
    for claim in &node.lean_sphincs_signers {
        let raw = raw_sphincs.iter().find(|(pk, m, _)| (*pk, *m) == *claim);
        holder(
            claim,
            raw.map(|(_, _, sig)| |out: &mut Out| out.sphincs_signature(sig)),
            &sphincs_children,
            &mut out,
        );
    }
    // The directly held matrix: its root, its vector digest, its rows and its membership vector.
    let direct = (!blobs.is_empty()).then(|| lean_da::commit(blobs));
    out.tag("da_witness");
    match &direct {
        Some((commitment, witness)) => {
            let root = commitment.root;
            out.0.push_str("direct ");
            out.bytes(&root);
            out.bytes(&lean_da::vector_digest(&lean_da::membership_vector(&root)));
            let rows: Vec<&[u64]> = witness.codewords.chunks(CODEWORD_SYMBOLS).collect();
            out.n(rows.len());
            for row in rows {
                out.n(row.len());
                for w in row {
                    write!(out.0, "{w:x} ").unwrap();
                }
            }
            out.es(&lean_da::membership_vector(&root));
        }
        None => out.0.push_str("none "),
    }
    out.tag("batch");
    let rounds = |name: &str| stream(name).map_or(vec![], |e| e[0].clone());
    out.es(&rounds("bc_sumcheck_msgs"));
    out.es(&stream("bc_star_hint").map_or(vec![F192::ZERO], |e| e[0].clone()));

    out.tag("streams");
    out.n(streams.len());
    for (name, entries) in &streams {
        out.tag(&format!("stream {name}"));
        out.n(entries.len());
        for entry in entries {
            out.es(entry);
        }
    }
    out.tag("end\n");

    let dir = std::env::var_os("LEANVM_GUEST_DIFF").expect("LEANVM_GUEST_DIFF names the output directory");
    let dir = std::path::Path::new(&dir);
    std::fs::create_dir_all(dir).unwrap();
    std::fs::write(dir.join(format!("{name}.txt")), out.0).unwrap();
    node
}

const LOG_INV_RATE: usize = leanvm_core::pcs::TEST_LOG_INV_RATE;

fn blob(seed: u64) -> Vec<u64> {
    let mut rng = StdRng::seed_from_u64(seed);
    (0..BLOB_SYMBOLS).map(|_| rng.random()).collect()
}

/// Two leaves, one of both schemes with a blob, one whose leanXMSS list is longer than a group of its digest
/// (`CLAIM_GROUP` claims), and a node over them with a blob and raw signatures, one of a claim both leaves make: the
/// leaves overlap in a claim of each scheme, so every coverage region of the node has duplicate slots, and its claims
/// are held directly and through each child. Then a node over the same leaves the other way round, with no blob and no
/// raw signature: it publishes its second child's DA digest (`da_pick` a child's slot, not the first).
#[test]
#[ignore]
fn guest_diff() {
    leanvm_core::init_prover();
    let wide = CLAIM_GROUP + 3;
    let xmss: Vec<_> = get_signers(wide + 2)
        .into_iter()
        .map(|(pk, sig)| (pk, message(), sig))
        .collect();
    let sphincs = get_lean_sphincs_signers(3);
    let left = export("left", vec![], xmss[..2].to_vec(), sphincs[..2].to_vec(), &blob(1));
    let right = export("right", vec![], xmss[1..wide + 1].to_vec(), sphincs[1..].to_vec(), &[]);
    let raw = vec![xmss[1].clone(), xmss[wide + 1].clone()];
    export("node", vec![left.clone(), right.clone()], raw, vec![], &blob(2));
    export("pass", vec![right, left], vec![], vec![], &[]);
}

/// The smallest case: a leaf of one leanXMSS signature.
#[test]
#[ignore]
fn guest_diff_leaf() {
    leanvm_core::init_prover();
    let xmss: Vec<_> = get_signers(1)
        .into_iter()
        .map(|(pk, sig)| (pk, message(), sig))
        .collect();
    export("leaf", vec![], xmss, vec![], &[]);
}
