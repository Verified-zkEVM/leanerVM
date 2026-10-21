/-
  LeanVM.E2E.Complete.DecodeSplit

  `DecodeHonest` (L9) split into its three reads: the children's count off `main`'s frame, each
  child's statement (`kidStmt`), each child's proof (`wVsLB` at the call's words).
-/

module

public import LeanVM.E2E.Complete.Interfaces

/-!
# The honest children's decoding, split

V_I's decoder (`End.decodeAt`) reads `main`'s frame `σ = valG L 1 (certOf 1)`: its children are
`decKids L.read σ wV`, `gLog (σ 6)` of them, child `c` the statement `kidStmt …` off the coverage
table and the proof `wV` reads at its `verify_sub` call's words (`decKid`). `decodeHonest_of`:
the count, the statements and the proofs give `DecodeHonest`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Node LeanVM.Guest
open LeanVM.Guest.B1.Main (decKid decKids kidStmt frameOf countOf cellAt gLog)

@[expose] public section

/-- `main`'s frame as V_I's decoder reads it. -/
noncomputable abbrev mainFrame {κ : ℕ} (L : MemImage κ) : Core.Val := Check.valG L 1 (certOf 1)

/-- The words of child `c`'s `verify_sub` call as the decoder reads them (`decKid`). -/
noncomputable def vsArgsAt {κ : ℕ} (L : MemImage κ) (c : ℕ) : List E :=
  [cellAt L.read (mainFrame L (.n 123)) (2 * c), cellAt L.read (mainFrame L (.n 123)) (2 * c + 1),
    mainFrame L (.n 63), mainFrame L (.n 64), mainFrame L (.n 65), mainFrame L (.n 66),
    mainFrame L (.n 133) * Protocol.Verifier.gen ^ (106 * c)]

/-- **The honest children decode** from the count, the statements and the proofs. -/
theorem decodeHonest_of {fr : Frames} {t : Trace Guest.guest} {w : NodeWitness}
    (hn : gLog (mainFrame t.image (.n 6)) = w.children.length)
    (hs : ∀ c (hc : c < w.children.length),
      kidStmt t.image.read (frameOf (mainFrame t.image)) (gLog (mainFrame t.image (.n 58)))
        (countOf t.image.read (mainFrame t.image)) c = w.children[c].statement)
    (hp : ∀ c (hc : c < w.children.length),
      Located.wVsLB (Value.tableSem (t.blakeRows blakeFree)) fr t.image (vsArgsAt t.image c) [] =
        w.children[c].proof) :
    DecodeHonest fr t w := by
  unfold DecodeHonest
  simp only [End.decodeAt, B1.Main.decWit, decKids]
  apply List.ext_getElem
  · simp [hn]
  · intro c h1 h2
    have hc : c < w.children.length := by simpa using h2
    simp only [List.getElem_map, List.getElem_range, decKid]
    rw [hs c hc]
    congr 1
    exact hp c hc

end
end LeanVM.E2E.Complete
