module

public import LeanVM.Cost.Bounds.Layout
public import LeanVM.Cost.Bounds.TranscriptReplay
public import LeanVM.Cost.Bounds.Sizes.Pruning
import all Statement.LeanIsa
import all Statement.LeanVmVerifier
import all LeanVM.Protocol.Extraction.Fast.AfterRoot
import all LeanVM.Protocol.Extraction.Fast.Extract

/-!
# Bounds: the extractor's parts, for the assembly

The facts and the parts' bounds `Bounds/Top.lean` assembles into the compiled extractor's price
(`extractorC_cost`):

* `bytecodeWords_length` (`16·2^ℓ` words); `afterRootLite_roots`: the replay's one root, at the
  ladder's first level (height `μ − 6 + R`, width `64`); `fastStacksFast_length_le`: at most one
  fast stack;
* the parts' closed bounds: `transcriptBound D L N` (`transcriptIndex_cost`, `N` queries,
  `N + 2 ≤ 2^D`, strings of at most `L` bytes), `tablesBound κ ℓ` (`runnerTables_cost`),
  `runBound κ ℓ` (`runWithTables_cost`, the step cap at most `2^35`), `fastBound μ R w cW`
  (`fastStacksFast_cost`, a column read at `17·w + cW`).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

public section

/-! ## Facts of the run -/

theorem bytecodeWords_length (prog : Semantics.Program) :
    (LeanVM.bytecodeWords prog).length = 16 * 2 ^ prog.logSize := by
  simp [LeanVM.bytecodeWords, List.length_flatMap]
  omega

theorem commitPure_roots {height width : ℕ} {s : ProgState} {t : Unit × ProgState}
    (h : commitPure height width s = some t) :
    ∃ root, t.2.roots = s.roots ++ [(root, height, width)] := by
  unfold commitPure at h
  split at h
  · split at h
    · obtain rfl := Option.some.inj h.symm
      exact ⟨_, rfl⟩
    · simp at h
  · simp at h

/-- **The stack's root**: `afterRootLite`'s one root, at the ladder's first level: height
`μ - 6 + R`, width `2^6`. -/
theorem afterRootLite_roots {bytecode : List K} {π : Proof} {L : LayoutLite} {R : ℕ}
    {st : ProgState} (h : afterRootLite bytecode π = some ((L, R), st)) :
    ∃ root, st.roots = [(root, L.stackLog - 6 + R, 64)] := by
  unfold afterRootLite at h
  cases hr : readSizesLite bytecode (initialState π) with
  | none => rw [hr] at h; simp at h
  | some r =>
    rw [hr, Option.bind_some] at h
    obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨⟨L', R'⟩, s'⟩ := r
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    obtain ⟨-, -, hroots, -⟩ := readSizesLite_some hr
    unfold commitStackPure at ht
    split at ht
    · rename_i level rest hla
      obtain ⟨hf, hR⟩ := ladder_head hla
      obtain ⟨root, hrt⟩ := commitPure_roots ht
      refine ⟨root, ?_⟩
      rw [hrt, hroots, hf, hR]
      rfl
    · simp at ht

/-- **At most one fast stack**: every lane's pruning step keeps at most as many survivors. -/
theorem fastStacksFast_length_le (μ R : ℕ) (W : ℕ → List K) : (fastStacksFast μ R W).length ≤ 1 := by
  have key : ∀ (f : List (List (Array K) × List ℕ) → ℕ → List (List (Array K) × List ℕ)),
      (∀ st u, (f st u).length ≤ st.length) →
      ∀ (l : List ℕ) (st : List (List (Array K) × List ℕ)), st.length ≤ 1 →
        (l.foldl f st).length ≤ 1 := by
    intro f hf l
    induction l with
    | nil => intro st h; exact h
    | cons u l ih => intro st h; exact ih _ ((hf st u).trans h)
  unfold fastStacksFast
  rw [List.length_map]
  exact key _ (fun st u ↦ pruneStep_single.1) _ _ (by simp)

/-! ## The budget -/

/-- The transcript's index (`transcriptIndex_cost`): `N` queries, `N + 2 ≤ 2^D`, strings of at
most `L` bytes. -/
@[expose] def transcriptBound (D L N : ℕ) : ℕ :=
  (23 * 8 + 31) * D + (replayStepBound (L + 136) D + 13) * N +
    (114 * (L + 136) + 12313) * (N + 1) + 470 +
    (N + 1) * ((23 * L * (D * D) + 60 * (D * D) + 69 * (L * D) + 208 * D + 94) +
      (25 * L + 192 * (D * D) + 595 * D + 161) + D * (17 + (60 + 23 * L) * (D + 2)) + 60) + 50

theorem transcriptBound_mono {D L N N' : ℕ} (h : N ≤ N') :
    transcriptBound D L N ≤ transcriptBound D L N' := by
  unfold transcriptBound
  gcongr

/-- The runner's tables (`runnerTables_cost`). -/
@[expose] def tablesBound (κ ℓ : ℕ) : ℕ :=
  (70 * κ + 374) * 2 ^ κ + (70 * ℓ + 374) * 2 ^ ℓ + 535 * ℓ + 830

/-- A stack's run (`runWithTables_cost`, the step cap at most `2^35`). -/
@[expose] def runBound (κ ℓ : ℕ) : ℕ := (stepPrice κ ℓ + 45) * 2 ^ 35 + 44 * 2 ^ κ + 1796

/-- The fast path (`fastStacksFast_cost`), a column read at `17·w + cW`, of `w` words. -/
@[expose] def fastBound (μ R w cW : ℕ) : ℕ :=
  64 * ((μ - 6) * (1520 * 2 ^ (μ - 6 + R) + 39583) + 102 * 2 ^ (μ - 6 + R) + 17509) +
    (17 * w + cW + 10 * w + 46) * 2 ^ (μ - 6 + R) + 1016 * 2 ^ μ + 1300

end

end LeanVM.Cost.Bounds
