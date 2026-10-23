/-
  LeanVM.Guest.B1.Place.OsCallsOk

  open_stacked's callee facts at the dispatch relation, on the honest trace.
-/

module

public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Whir.BrCaps

/-!
# The body's calls at `osCR`

`osSp c tr A`: the callees placed apart, at their honest arguments and returns: level `l`'s
squeeze loop, its `opening_queries`, its residual loop. `OsNames c`: the configuration's callee
names are the table's (`osKindOf`), at the kinds the body calls them with, and the others are
not in it (decided per configuration). `osCallsOk_honest`: on memory holding the honest buffers,
the body's calls hold at `osCR rd (osSp c tr A)`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- Level `l`'s squeeze loop's arguments. -/
abbrev osSqArgs (c : OsCfg) (A : OsAt) (l : ℕ) : List E :=
  [1, gen ^ (lvAt c l).squeezes, A.sqz l, A.P.qpos, A.P.qbp]

/-- Level `l`'s `opening_queries` arguments. -/
abbrev osQArgs (c : OsCfg) (tr : OsTr) (A : OsAt) (l : ℕ) : List E :=
  [A.P.caps * gen ^ (4 * (lvAt c l).capOff), A.P.flags * gen ^ (lvAt c l).capOff, (tr.L l).lam,
    (tr.L l).lam ^ (lvAt c l).queries, A.P.qbp * gen ^ (lvAt c l).posOff, A.wp l,
    gen ^ ((lvAt c l).queries / (1 + if l = 0 then 1 else 0))]

/-- Level `l`'s residual loop's arguments. -/
abbrev osResArgs (c : OsCfg) (A : OsAt) (l : ℕ) : List E :=
  [1, gen ^ ((lvAt c l).queries / 2), A.P.qpos, A.P.qw, A.BD, A.rc l]

/-- **The callees placed apart**, at their honest arguments and returns. -/
def osSp (c : OsCfg) (tr : OsTr) (A : OsAt) : String → List E → List E → Prop := fun f a r ↦
  ∃ l < c.levels.length,
    (f = c.sqLoop l ∧ a = osSqArgs c A l ∧ r = []) ∨
    (f = osQueriesName l (lvAt c l) ∧ a = osQArgs c tr A l ∧ r = [(tr.L l).enforced]) ∨
    (f = c.resLoop l ∧ a = osResArgs c A l ∧ r = [])

/-- **The configuration's callee names**, decided per configuration. -/
structure OsNames (c : OsCfg) : Prop where
  ood : ∀ i < c.levels.length, i ≠ c.yrLevel →
    osKindOf ("opening_ood_point__L" ++ natStr (lvAt c i).logCols) = some (.ood (lvAt c i).logCols)
  grind : ∀ i < c.levels.length,
    osKindOf ("grind_check__L" ++ natStr (lvAt c i).grind) = some (.grind Whir.queryGrindingBits)
  fm : osKindOf ("opening_final_message__L" ++ natStr c.yrLen) = some (.fm c.yrLen)
  rw : ∀ i < c.levels.length,
    osKindOf ("opening_row_weights__L" ++ natStr (lvAt c i).folds ++ "_L" ++
      natStr (if i = 0 then 1 else 0)) = some (.rw (lvAt c i).folds (if i = 0 then 1 else 0))
  cap : ∀ i < c.levels.length,
    osKindOf ("verify_merkle_cap__L" ++ natStr (lvAt c i).capDepth) = some (.cap (lvAt c i).capDepth)
  ffm : osKindOf ("fold_final_msg__L" ++ natStr c.yrLog) = some (.ffm c.yrLog)
  sq : ∀ i < c.levels.length, osKindOf (c.sqLoop i) = none
  q : ∀ i < c.levels.length, osKindOf (osQueriesName i (lvAt c i)) = none
  res : ∀ i < c.levels.length, osKindOf (c.resLoop i) = none
  il : ∀ i < c.levels.length,
    2 ^ rwLo (lvAt c i).folds + 2 ^ ((lvAt c i).folds - rwLo (lvAt c i).folds) ≤ c.maxIl
  cdd : ∀ i < c.levels.length, (lvAt c i).capDepth ≤ (lvAt c i).depth

theorem osKindOf_fold : osKindOf "opening_fold" = some .fold := by
  simp [osKindOf, osKindTable]
theorem osKindOf_can : osKindOf "assert_canonical" = some .can := by
  simp [osKindOf, osKindTable, List.lookup]

/-- **The body's calls hold at `osCR`** on memory holding the honest buffers. -/
theorem osCallsOk_honest {c : OsCfg} {tr : OsTr} {μ r : ℕ} {cfg : List Whir.Level}
    (hF : CandFacts c μ r cfg) (h : TrFit c tr) (hs : OsSizes c) {target : E} {S : KState}
    {xs : List E} {os : List Opening} {root : Digest} (hrun : TrRun c μ r target S xs os root tr)
    (hcaps : CapsAgree μ r target S xs os root) (hN : OsNames c) {rd : Reader} {A : OsAt}
    (hm : OsMem rd A c tr) (hC : ReadsAt rd A.P.caps (capsC c tr))
    (hFl : ReadsAt rd A.P.flags (flagsC c tr))
    (hW : ∀ i < c.levels.length, ReadsAt rd (A.wp i) (wpC c tr i)) :
    OsCallsOk (osCR rd (osSp c tr A)) rd A c tr := by
  refine ⟨fun _ _ hm' ↦ osCR_named osKindOf_fold hm', fun i hi ↦ ?_, fun i hi _ ↦ ?_, ?_⟩
  · refine ⟨fun _ _ hm' ↦ osCR_named osKindOf_fold hm', fun _ _ hm' ↦ osCR_named osKindOf_can hm',
      fun hne _ _ hm' ↦ osCR_named (hN.ood i hi hne) hm', fun _ _ hm' ↦ osCR_named (hN.grind i hi) hm',
      fun _ _ _ hm' ↦ osCR_named hN.fm hm', fun _ ↦ ?_, ?_, ?_, ?_⟩
    · exact osCR_special (hN.sq i hi) ⟨i, hi, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact osCR_named (hN.rw i hi) (rw_meaning_at hF h hm.fixed hi (hW i hi) (hN.il i hi))
    · exact osCR_named (hN.cap i hi) (cap_meaning_at h hs hrun hcaps hC hFl hi (hN.cdd i hi))
    · have hq : osSp c tr A (osQueriesName i (lvAt c i)) (osQArgs c tr A i) [(tr.L i).enforced] :=
        ⟨i, hi, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
      exact osCR_special (hN.q i hi) hq
  · exact osCR_special (hN.res i hi) ⟨i, hi, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
  · exact osCR_named hN.ffm (ffm_meaning_at hF h hs hm.fixed hm.T)

end
end LeanVM.Guest.B1
