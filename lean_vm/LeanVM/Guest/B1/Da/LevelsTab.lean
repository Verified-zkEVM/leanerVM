/-
  LeanVM.Guest.B1.Da.LevelsTab

  `da_levels`' eleven specializations and their level loops, and the soundness of a checked
  specialization.
-/

module

public import LeanVM.Guest.B1.Da.Levels

/-!
# The specializations of `da_levels`

`dlTab` lists, for `k ≤ 10`, the specialization `da_levels__L{2^k}_L{k}`, its core function
and its `k` level loops. `dlEntryOk k` checks the entry (`dlOk`, every loop's `lvlOk`, the names);
the `LevelsChk*` modules evaluate it, and `dl_sound` turns a checked entry into
`MeaningDaLevels k`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

/-- The specializations: `k`, the name, the core function, the level loops. -/
def dlTab : List (ℕ × String × ℕ × List String) :=
  [(0, "da_levels__L1_L0", 364, []),
    (1, "da_levels__L2_L1", 365, ["__loop311"]),
    (2, "da_levels__L4_L2", 366, ["__loop312", "__loop313"]),
    (3, "da_levels__L8_L3", 367, ["__loop314", "__loop315", "__loop316"]),
    (4, "da_levels__L16_L4", 368, ["__loop317", "__loop318", "__loop319", "__loop320"]),
    (5, "da_levels__L32_L5", 369, ["__loop321", "__loop322", "__loop323", "__loop324", "__loop325"]),
    (6, "da_levels__L64_L6", 370, ["__loop326", "__loop327", "__loop328", "__loop329", "__loop330", "__loop331"]),
    (7, "da_levels__L128_L7", 361, ["__loop304", "__loop305", "__loop306", "__loop307", "__loop308", "__loop309", "__loop310"]),
    (8, "da_levels__L256_L8", 371, ["__loop332", "__loop333", "__loop334", "__loop335", "__loop336", "__loop337", "__loop338", "__loop339"]),
    (9, "da_levels__L512_L9", 372, ["__loop340", "__loop341", "__loop342", "__loop343", "__loop344", "__loop345", "__loop346", "__loop347", "__loop348"]),
    (10, "da_levels__L1024_L10", 373, ["__loop349", "__loop350", "__loop351", "__loop352", "__loop353", "__loop354", "__loop355", "__loop356", "__loop357", "__loop358"])]
/-- A level loop, found and checked. -/
noncomputable def loopOk (f : String) (offA offB : ℕ) : Bool :=
  match coreProgram.indexOf? f with
  | some j => decide (j < coreProgram.length) && lvlOk (coreProgram.getD j default) f offA offB
  | none => false

/-- **Entry `k` of `dlTab`, checked.** -/
noncomputable def dlEntryOk (k : ℕ) : Bool :=
  let e := dlTab.getD k (0, "", 0, [])
  decide (e.1 = k) && decide (e.2.1 = daLevelsName k) &&
  decide (coreProgram.indexOf? e.2.1 = some e.2.2.1) && decide (e.2.2.1 < coreProgram.length) &&
  dlOk (coreProgram.getD e.2.2.1 default) k e.2.2.2 &&
  (List.range k).all fun lvl => loopOk (e.2.2.2.getD lvl "") (off k lvl) (off k (lvl + 1))

end
end LeanVM.Guest.B1.Da
