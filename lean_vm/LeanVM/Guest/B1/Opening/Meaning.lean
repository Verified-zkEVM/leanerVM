/-
  LeanVM.Guest.B1.Opening.Meaning

  The interface of B1's WHIR opening functions: what each computes on the carried sponge, and
  the statement that its core IR computes it.
-/

module

public import LeanVM.Guest.B1.Common.Sponge

/-!
# The stacked WHIR opening's helpers: meanings (TRIAGE G #35-38)

For each function of the guest (`lean_ethereum.py` at leanVM `3375f7a13`, G below) its meaning
on its argument and return words, the sponge as the guest carries it (`Fs`), and `…_Spec`, the
statement that its core IR relation is that meaning (proved as `…_holds`). The Spec steps they
are (`foldRounds`, `tailRounds`, V:1691, 1702; `sampleN`; `readN` and `grindP`) are the `…_run`
theorems of `B1/Opening/`.

| function | G | meaning |
| --- | --- | --- |
| `opening_fold` | 1103-1115 | squeeze with two scalars waiting, fold the quadratic, read the next `c0, c2` (left waiting) |
| `opening_ood_point__L{n}` | 1118-1129 | `n` challenges, the first from a permutation of the given rate cells |
| `opening_final_message__L{n}` | 1132-1150 | absorb the final message's `n` words and the nonce (`dsPowNonce`), permute |
| `opening_row_weights__L{f}_L{r}` | 1153-1176 | the row's `eqKernel` weights as two tensor factors, reversed at level 0 |
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `opening_fold` (G:1103-1115, TRIAGE #35) -/

/-- **`opening_fold(fs0..fs4, w0, w1, cursor, c0, c1, c2)`**: from the carried capacity
(canonical cells) with the scalars `w0`, `w1` waiting (`dsObserve`), the challenge `r` is
squeezed, the claim folded to `(c2·r + c1)·r + c0` (`polyEval [c0, c1, c2] r`), and the two
stream words at the cursor, the next round's `c0`, `c2`, are read (they wait in the next sponge,
which the next call packs); the function returns the capacity after the squeeze, the cursor two
words on, the claim, the two words and `r`. -/
def MeaningOpeningFold (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, w0, w1, cur, c0, c1, c2], rets =>
      AllCanonical [f0, f1, f2, f3, f4] ∧ ∃ d0 d2 : E, ReadsAt rd cur [d0, d2] ∧
        let r := (⟨[f0, f1, f2, f3, f4], [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).squeeze
        rets = r.2.cap ++ [cur * gen ^ 2, (c2 * r.1 + c1) * r.1 + c0, d0, d2, r.1]
  | _, _ => False

/-- `opening_fold`'s core IR is its meaning. -/
def opening_fold_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "opening_fold" args rets ↔ MeaningOpeningFold rd args rets

/-! ## `opening_ood_point` (G:1118-1129, TRIAGE #36) -/

/-- **`opening_ood_point(fs0..fs4, r0..r7, point, n)`** (`n ≥ 1`): the rate cells `r0..r7` and the
capacity are canonical; the first coordinate is the challenge of their permutation, the other
`n - 1` are squeezed with nothing waiting; the coordinates are stored at `point`, and the
function returns the final capacity. With `r0..r7 = rateOf pend`, it is `sampleN n` from the
sponge carried as `⟨cap, pend⟩`. -/
def MeaningOpeningOodPoint (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, r0, r1, r2, r3, r4, r5, r6, r7, point], rets =>
      AllCanonical [r0, r1, r2, r3, r4, r5, r6, r7, f0, f1, f2, f3, f4] ∧
        let S := permOf [r0, r1, r2, r3, r4, r5, r6, r7, f0, f1, f2, f3, f4]
        let rest := (⟨capOf S, []⟩ : Fs).squeezeN (n - 1)
        ReadsAt rd point (challengeOf S :: rest.1) ∧ rets = rest.2.cap
  | _, _ => False

/-- `opening_ood_point__L{n}`'s core IR is its meaning, `6 ≤ n ≤ 22`. -/
def opening_ood_point_Spec : Prop :=
  ∀ n, 6 ≤ n → n ≤ 22 → ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd ("opening_ood_point__L" ++ toString n) args rets ↔
      MeaningOpeningOodPoint n rd args rets

/-! ## `opening_final_message` (G:1132-1150, TRIAGE #37) -/

/-- **`opening_final_message(fs0..fs4, w0, w1, cursor, out, n)`**: from the carried capacity
(canonical cells) with `w0`, `w1` waiting, the `n` stream words at the cursor (the final message,
stored at `out`) are absorbed, then the next word, the nonce, with the tag `dsPowNonce`, and the
sponge permutes; the function returns that state's first cell (whose first limb `grind_check`
reads, `challengeOf_limb0`), its capacity, the cursor past the nonce and the nonce. -/
def MeaningOpeningFinalMessage (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, w0, w1, cur, out], rets =>
      AllCanonical [f0, f1, f2, f3, f4] ∧ ∃ (ms : List E) (nonce : E), ms.length = n ∧
        ReadsAt rd cur (ms ++ [nonce]) ∧ ReadsAt rd out ms ∧
        let s := ((⟨[f0, f1, f2, f3, f4], [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).absorbAll ms
          dsObserve).absorb nonce dsPowNonce
        rets = [cellsOfState s.perm false 0] ++ capOf s.perm ++ [cur * gen ^ (n + 1), nonce]
  | _, _ => False

/-- `opening_final_message__L{n}`'s core IR is its meaning, `n ∈ {4, 8, 16, 32}`. -/
def opening_final_message_Spec : Prop :=
  ∀ n ∈ [4, 8, 16, 32], ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd ("opening_final_message__L" ++ toString n) args rets ↔
      MeaningOpeningFinalMessage n rd args rets

/-! ## `opening_row_weights` (G:1153-1176, TRIAGE #38) -/

/-- Slot `i` of a run of `2^m`, reversed when `rev = 1`. -/
def rwSlot (m rev i : ℕ) : ℕ := if rev = 1 then 2 ^ m - 1 - i else i

/-- The low factor's coordinates: `min folds 3`. -/
def rwLo (folds : ℕ) : ℕ := if folds / 3 = 0 then folds else 3

/-- **`opening_row_weights(point, out, folds, reverse)`**: the `folds` words at `point`; the low
factor `out[i] = eqKernel(point[..lo])[slot i]`, `i < 2^lo`, and the high factor
`out[2^lo + i] = eqKernel(point[lo..])[slot i]`, `i < 2^(folds - lo)`, the slots reversed at
`reverse = 1`: weight `i` of the row is `out[i % 2^lo] · out[2^lo + i / 2^lo]`, entry `i` (or
`2^folds - 1 - i`) of `eqKernel` (V:642). -/
def MeaningOpeningRowWeights (folds rev : ℕ) (rd : Reader) : List E → List E → Prop
  | [point, out], rets =>
      rets = [] ∧ ∃ rs : List E, rs.length = folds ∧ ReadsAt rd point rs ∧
        (∀ i < 2 ^ rwLo folds,
          LoadHolds rd out i ((eqKernel (rs.take (rwLo folds))).getD (rwSlot (rwLo folds) rev i) 0)) ∧
        ∀ i < 2 ^ (folds - rwLo folds),
          LoadHolds rd out (2 ^ rwLo folds + i)
            ((eqKernel (rs.drop (rwLo folds))).getD (rwSlot (folds - rwLo folds) rev i) 0)
  | _, _ => False

/-- `opening_row_weights__L6_L1` and `__L4_L0`'s core IR are their meanings. -/
def opening_row_weights_Spec : Prop :=
  (∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "opening_row_weights__L6_L1" args rets ↔
      MeaningOpeningRowWeights 6 1 rd args rets) ∧
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "opening_row_weights__L4_L0" args rets ↔
      MeaningOpeningRowWeights 4 0 rd args rets

end
end LeanVM.Guest.B1
