/-
  LeanVM.E2E.Vis.DaDecoder

  W-vis, P3b: the DA potential stopped at the format event. A hidden query is charged E5's full
  rate: unlike T1's and W6's decoders, E5's anchor does not follow a chain from the label, so a
  hidden input can complete a root after a hidden entry with a hidden-prefix answer.
-/

module

public import LeanVM.E2E.Vis.Decoder
public import LeanVM.E2E.Da.Potential

/-!
# The DA potential, stopped (W-vis, P3b)

E5's potential (`daPot`, `LeanVM.E2E.Da.Potential`) gives a term to every *anchor*: an entry
whose input completes a root, `d ‖ obsBlock ρ 1` with `d` the answer of an earlier entry whose
input is `X ‖ obsBlock ρ 0` (`DaRootOf`). Nothing asks the earlier entry to be on a challenge
chain from the label, nor to be non-hidden.

**Why hidden queries pay the full rate.** A hidden anchor `d ‖ obsBlock ρ 1` has `d` a hidden
prefix (`inPfx_of_hid_digest_append`), so its first-half entry answers a hidden prefix
(`exists_inPfx_of_daRootOf_hid`). Without the format event that entry is hidden itself
(`hid_of_daRootOf_hid`), but nothing excludes such an entry:

* a parameter-derivation-shaped query `paramPrefix ‖ obsBlock ρ 0` from `k0` on (`DerivShape`,
  which `FormatI` leaves out) answered by `p ‖ a`; or
* a key-generation entry `p ‖ a ‖ obsBlock ρ 0` answered by a hidden prefix.

After either, the hidden query `p ‖ a ‖ obsBlock ρ 1` is an anchor. Its term averages to the
probability that 14 challenges accept rows committed to `ρ` with a non-codeword, about
`1/|E|`, which exceeds the failure term `4(|ℓ| + 1)/|Digest|`. Both situations have probability
about `2^-128` or less, but they are not excluded by the hypotheses of a step bound (the format
event, a hidden key generation). By the same token `daPot` is not at most `ind (FailDA pc ℓ)` on
a log of hidden entries.

So (decision with the W-vis lead) a hidden query is charged E5's full rate, as a non-hidden
one: `daPotStop_step` is `daPot_step` for the stopped potential `daPot · 1[¬ FormatI]`, for
every fresh input. In the end bound the DA term is `Q · 14/2^192` rather than
`Q_v · 14/2^192` (about `2^-111` at the lifetime parameters).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

variable {nx ns : ℕ} [Sphincs.Params]

/-- **The DA potential's step, stopped at the format event** (P3b): every fresh query, hidden or
not, raises `daPot · 1[¬ FormatI]`, in expectation, by at most E5's rate
`14/|E| + 4 (|ℓ| + 1)/|Digest|`. -/
theorem daPotStop_step (keys : Keys nx ns) (k0 : ℕ) (pc : LeanDa.Digest) (ℓ : Log) (t : Bytes) :
    (∑ u, daPot pc (ℓ ++ [(t, u)]) * ind (¬ FormatI keys k0 (ℓ ++ [(t, u)]))) /
        Fintype.card Digest ≤
      daPot pc ℓ * ind (¬ FormatI keys k0 ℓ) +
        (14 * (Fintype.card E : ℝ≥0∞)⁻¹ +
          ((4 * (ℓ.length + 1) : ℕ) : ℝ≥0∞) / Fintype.card Digest) :=
  sum_stop_le_of_step keys k0 fun _ ↦ daPot_step

/-- **A hidden anchor needs a hidden-prefix answer**: a hidden input that completes a root in
`ℓ` has its first-half entry answering a hidden prefix, that entry's input ending in the root's
first observation block. -/
theorem exists_inPfx_of_daRootOf_hid {keys : Keys nx ns} {ℓ : Log} {t : Bytes}
    {ρ : LeanDa.Digest} (hr : DaRootOf ℓ t ρ) (ht : Hid keys t) :
    ∃ e ∈ ℓ, InPfx keys e.2 ∧ e.1.drop 32 = obsBlock ρ 0 := by
  obtain ⟨d, e, rfl, hf, he⟩ := hr
  have hd := inPfx_of_hid_digest_append (by rw [obsBlock_length]; decide)
    (by rw [obsBlock_length]; decide) ht
  have hmem := List.mem_of_find?_eq_some hf
  have hed : e.2 = d := by simpa using List.find?_some hf
  exact ⟨e, hmem, hed ▸ hd, he⟩

/-- Without the format event (non-hidden entries answer no hidden prefix), a hidden anchor's
first-half entry is hidden: the cases `daPotStop_step` pays for. -/
theorem hid_of_daRootOf_hid {keys : Keys nx ns} {ℓ : Log} (hN : NotHidOut keys ℓ) {t : Bytes}
    {ρ : LeanDa.Digest} (hr : DaRootOf ℓ t ρ) (ht : Hid keys t) :
    ∃ e ∈ ℓ, Hid keys e.1 ∧ InPfx keys e.2 ∧ e.1.drop 32 = obsBlock ρ 0 := by
  obtain ⟨e, he, hp, hd⟩ := exists_inPfx_of_daRootOf_hid hr ht
  exact ⟨e, he, by_contra fun hn ↦ hN e he hn hp, hp, hd⟩

end
end LeanVM.E2E
