/-
  LeanVM.Guest.B1.Terminal.TermKids

  `check_opening_terminal`'s callees on the honest words: the prefix chains, the public input's
  chain, the selector tables, the column selectors, the outputs' chain, the ring switch's weight,
  each complete, placed.
-/

module

public import LeanVM.Guest.B1.Terminal.SelComplete
public import LeanVM.Guest.B1.Terminal.KidsDep
public import LeanVM.Guest.B1.Terminal.EqPrefixIn
public import LeanVM.Guest.B1.Terminal.Loop15Complete
public import LeanVM.Guest.B1.Ring.WeightComplete
public import LeanVM.Guest.B1.Terminal.Holds

/-!
# The terminal's callees

The caller's words: `TermBases` names the bases of the pointer arguments (`termArgs`), `TermRegion`
the words the terminal and its callees read there. `TermData` gathers the honest data: the bus
point `zs`, the tables' point `chis`, the outputs' point, the ring switch's point and
coefficients, the terminal point `x`, the committed columns' logs `KC` and offsets `OF`, the memory's
log `m` and `KECCAK`'s `τ`.

The honest buffers: `eqChain as bs`, the prefix products `eq_prefix_chain` writes; `piW`, the public
input's chain. `termKids`: the 105 callees in order, each column selector reading the selector
tables' result (`selKid`); `termKids_complete`: each is complete, placed (`eqc_kid_complete`,
`l15_kid_complete`, B1-c's `selector_tables_completeAt`, `cs_completeAt`, `rsw_completeAt`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)
open Finset

@[expose] public section

/-! ## The caller's words -/

/-- The bases of `check_opening_terminal`'s pointer arguments. -/
structure TermBases where
  zeta : ℕ
  chi : ℕ
  cplen : ℕ
  lamPool : ℕ
  off : ℕ
  kap : ℕ
  zv : ℕ
  ct : ℕ
  pt : ℕ
  pt1 : ℕ

/-- `check_opening_terminal`'s arguments, its pointers at their bases. -/
def termArgs (B : TermBases) (rm gmu gzcn glm gtau lamOut inner yr target : E) : List E :=
  [ofK (gpow B.zeta), ofK (gpow B.chi), rm, gmu, gzcn, glm, gtau, ofK (gpow B.cplen), lamOut,
    ofK (gpow B.lamPool), ofK (gpow B.off), ofK (gpow B.kap), ofK (gpow B.zv), ofK (gpow B.ct),
    ofK (gpow B.pt), ofK (gpow B.pt1), inner, yr, target]

/-- **The caller's words the terminal reads**: the bus point (`nz` words) and the tables' point
(`nc`), the claims' lengths and batching powers, the columns' offsets and logs, the outputs'
point and the ring switch's (`τ + 6` words each, the latter at `z_vals·g^39`), the ring map's
coefficients, the terminal point and its complements. -/
def TermRegion (B : TermBases) (nz nc τ : ℕ) (i : ℕ) : Prop :=
  (B.zeta ≤ i ∧ i < B.zeta + nz) ∨ (B.chi ≤ i ∧ i < B.chi + nc) ∨
    (B.cplen ≤ i ∧ i < B.cplen + 162) ∨ (B.lamPool ≤ i ∧ i < B.lamPool + 165) ∨
    (B.off ≤ i ∧ i < B.off + 99) ∨ (B.kap ≤ i ∧ i < B.kap + 99) ∨
    (B.zv ≤ i ∧ i < B.zv + (τ + 6)) ∨ (B.zv + 39 ≤ i ∧ i < B.zv + 39 + (τ + 6)) ∨
    (B.ct ≤ i ∧ i < B.ct + 64) ∨ (B.pt ≤ i ∧ i < B.pt + 40) ∨ (B.pt1 ≤ i ∧ i < B.pt1 + 40)

/-- The honest data the terminal's callees use. -/
structure TermData where
  B : TermBases
  rm : E
  gmu : E
  gzcn : E
  glm : E
  gtau : E
  zs : List E
  chis : List E
  outPt : List E
  ringPoint : List E
  coeffs : List E
  x : List E
  KC : List ℕ
  OF : List ℕ
  m : ℕ
  τ : ℕ

/-! ## The honest buffers -/

/-- `1 + x`, zero-padded: the words at `point1`. -/
def p1Of (x : List E) : List E := (padPoint x).map (1 + ·)

/-- The selector tables' point. -/
def pt28 (x : List E) : List E := (padPoint x).take 28

/-- The selector tables' complements. -/
def pt128 (x : List E) : List E := (p1Of x).take 28

/-- The prefix products `eq_prefix_chain(chain, 1, a, b1, g^|as|)` writes. -/
def eqChain (as bs : List E) : List E := (List.range (as.length + 1)).map (prefixProd 1 as bs)

/-- The public input's chain: `1`, then `(rm + ps[0])·Π_{0 < i < k} ps[i]`, `1 ≤ k ≤ m`. -/
def piW (rm : E) (ps : List E) (m : ℕ) : List E :=
  (List.range (m + 1)).map fun k => if k = 0 then 1 else (rm + ps.getD 0 0) * ∏ i ∈ Ico 1 k, ps.getD i 0

theorem p1Of_length {x : List E} (h : x.length ≤ termPointCap) : (p1Of x).length = 40 := by
  simp [p1Of, padPoint_length h]

theorem eqChain_length (as bs : List E) : (eqChain as bs).length = as.length + 1 := by simp [eqChain]

theorem piW_length (rm : E) (ps : List E) (m : ℕ) : (piW rm ps m).length = m + 1 := by simp [piW]

theorem piW_getD {rm : E} {ps : List E} {m k : ℕ} (hk : k ≤ m) :
    (piW rm ps m).getD k 0 = if k = 0 then 1 else (rm + ps.getD 0 0) * ∏ i ∈ Ico 1 k, ps.getD i 0 := by
  rw [List.getD_eq_getElem _ _ (by simp [piW]; omega)]
  simp [piW]

theorem ofK_gpow_mul_gen (b c : ℕ) : ofK (gpow b) * gen ^ c = ofK (gpow (b + c)) := by
  rw [gen_pow_eq_ofK, ← ofK_mul, gpow, gpow, gpow, pow_add]

theorem regionL_cons {L : Main.Layout} (q : ℕ × List E) {i : ℕ} (h : RegionL L i) :
    RegionL (q :: L) i := by
  obtain ⟨q', hq, h⟩ := h
  exact ⟨q', List.mem_cons_of_mem _ hq, h⟩

theorem regionL_head {L : Main.Layout} {b : ℕ} {xs : List E} {i : ℕ} (h1 : b ≤ i)
    (h2 : i < b + xs.length) : RegionL ((b, xs) :: L) i :=
  ⟨(b, xs), List.mem_cons_self, h1, h2⟩

/-! ## The callees -/

/-- The value of committed column `c`'s selector: the eq weight of its offset's bits above its log
against the point's. -/
def selRet (x : List E) (KC OF : List ℕ) (c : ℕ) : E :=
  Tables.bitsEq ((List.range (28 - KC.getD c 0)).map fun i => (OF.getD c 0).testBit (KC.getD c 0 + i))
    ((pt28 x).drop (KC.getD c 0)) ((pt128 x).drop (KC.getD c 0))

/-- `selector_tables`' result among the results before. -/
def stRes (pv : List (List E × Main.Layout)) : List E × Main.Layout := pv.getD 3 ([], [])

/-- **Committed column `c`'s selector**, on `selector_tables`' result (entered when it is one). -/
noncomputable def selKid (D : TermData) (c : ℕ) : KidD := fun pv =>
  open Classical in
  ⟨Tables.lName "column_selector" (D.KC.getD c 0),
    decide (Tables.stOut D.B.pt D.B.pt1 (pt28 D.x) (pt128 D.x) (stRes pv).1 (stRes pv).2),
    [gen ^ D.OF.getD c 0, (stRes pv).1.getD 0 0, (stRes pv).1.getD 1 0],
    if Tables.stOut D.B.pt D.B.pt1 (pt28 D.x) (pt128 D.x) (stRes pv).1 (stRes pv).2 then
      (stRes pv).2 ++ Tables.stLin D.B.pt D.B.pt1 (pt28 D.x) (pt128 D.x) else [],
    Returns [selRet D.x D.KC D.OF c]⟩

/-- **`check_opening_terminal`'s callees, in order**, its buffers from `b0`. -/
noncomputable def termKids (Lin : Main.Layout) (D : TermData) (b0 : ℕ) : List KidD :=
  [fun _ => ⟨"eq_prefix_chain", true,
      [ofK (gpow b0), word 1 0 0, ofK (gpow D.B.zeta), ofK (gpow D.B.pt1), D.gmu],
      (b0, eqChain D.zs ((p1Of D.x).take D.zs.length)) :: Lin, Returns []⟩,
    fun _ => ⟨"eq_prefix_chain", true,
      [ofK (gpow (b0 + 35)), word 1 0 0, ofK (gpow D.B.chi), ofK (gpow D.B.pt1), D.gzcn],
      (b0 + 35, eqChain D.chis ((p1Of D.x).take D.chis.length)) :: Lin, Returns []⟩,
    fun _ => ⟨"__loop15", decide (word 2 0 0 + D.glm ≠ 0),
      [word 2 0 0, D.glm, ofK (gpow (b0 + 70)), ofK (gpow D.B.pt1)],
      (b0 + 70, piW D.rm (p1Of D.x) D.m) :: Lin, Returns []⟩,
    fun _ => ⟨"selector_tables", true, [ofK (gpow D.B.pt), ofK (gpow D.B.pt1)],
      Tables.stLin D.B.pt D.B.pt1 (pt28 D.x) (pt128 D.x),
      Tables.stOut D.B.pt D.B.pt1 (pt28 D.x) (pt128 D.x)⟩] ++
  (List.range Tables.nCommittedCols).map (selKid D) ++
  [fun _ => ⟨"eq_prefix_chain", true,
      [ofK (gpow (b0 + 105)), word 1 0 0, ofK (gpow D.B.zv), ofK (gpow D.B.pt1), D.gtau * word 64 0 0],
      (b0 + 105, eqChain D.outPt ((p1Of D.x).take D.outPt.length)) :: Lin, Returns []⟩,
    fun _ => ⟨"ring_switch_weight", true,
      [ofK (gpow D.B.zv) * word 549755813888 0 0, ofK (gpow D.B.pt1), ofK (gpow D.B.ct),
        D.gtau * word 64 0 0],
      [(D.B.zv + 39, D.ringPoint), (D.B.pt1, (p1Of D.x).take (D.τ + 6)), (D.B.ct, D.coeffs)],
      Returns [ringWeight D.ringPoint (((p1Of D.x).take (D.τ + 6)).map (1 + ·)) D.coeffs]⟩]

theorem termKids_length (Lin : Main.Layout) (D : TermData) (b0 : ℕ) :
    (termKids Lin D b0).length = 105 := by
  simp [termKids, Tables.nCommittedCols]

/-! ## Each callee, complete -/

theorem eqc_pure : coreProgram.PureIn ("eq_prefix_chain" :: eqPrefixRunNames) :=
  Tables.pureIn_of_pureInB (by decide +kernel)

theorem l15_pure : coreProgram.PureIn ["__loop15"] := Tables.pureIn_of_pureInB (by decide +kernel)

theorem low_rc {κ : ℕ} (hκ : 6 ≤ κ) {rd : Reader} (hl : LowDef κ rd) {n : ℕ} (hn : n ≤ 40) :
    RangeChecked rd (gen ^ n) (gen ^ 40) := by
  have h40 : 40 < 2 ^ κ := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)
  have l1 := hl n (by omega)
  have l2 := hl (40 - n) (by omega)
  have a : ∀ a, (gen ^ a).limb 0 * gpow 0 = gpow a := fun a => by
    rw [gen_pow_eq_ofK, Main.addr_ofK, Nat.add_zero]
  obtain ⟨t1, h1⟩ := Option.isSome_iff_exists.mp l1
  obtain ⟨t2, h2⟩ := Option.isSome_iff_exists.mp l2
  exact ⟨gen ^ (40 - n), t1, t2, ⟨gen_pow_isInK n, by rw [a]; exact h1⟩,
    by rw [← pow_add, Nat.add_sub_cancel' hn], ⟨gen_pow_isInK _, by rw [a]; exact h2⟩⟩

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A prefix chain, complete, placed**: on the runs `as` at `g^ba` and `bs` at `g^bb`, its
chain `eqChain as bs` at `g^b`. -/
theorem eqc_kid_complete (κ : ℕ) (hκ : 6 ≤ κ) {b ba bb : ℕ} {as bs : List E} {cg : E}
    {L : Main.Layout} (hn : as.length ≤ 40) (hbs : bs.length = as.length) (hcg : cg = gen ^ as.length)
    (hrd : ∀ rd, LowDef κ rd → MemL rd L → ReadsAt rd (ofK (gpow ba)) as ∧ ReadsAt rd (ofK (gpow bb)) bs)
    (hR : ∀ i, (ba ≤ i ∧ i < ba + as.length) ∨ (bb ≤ i ∧ i < bb + as.length) → RegionL L i) :
    CompleteAtD fs cert κ "eq_prefix_chain" ((b, eqChain as bs) :: L)
      [ofK (gpow b), word 1 0 0, ofK (gpow ba), ofK (gpow bb), cg] (Returns []) := by
  refine Lift.completeAtD_of_relIn eqc_pure List.mem_cons_self fun rd hl hm => ?_
  have hm0 : ReadsAt rd (ofK (gpow b)) (eqChain as bs) := hm _ List.mem_cons_self
  have hmL : MemL rd L := fun q hq => hm q (List.mem_cons_of_mem _ hq)
  obtain ⟨ha, hb⟩ := hrd rd hl hmL
  subst hcg
  refine eqc_relIn hn (fun i hi => ?_) ((eq_prefix_chain_holds rd _ _).mpr
    ⟨rfl, low_rc hκ hl hn, as.length, by omega, rfl, as, bs, rfl, hbs, ha, hb, fun j hj => ?_⟩)
  · rcases hi with hi | hi
    · exact regionL_head hi.1 (by rw [eqChain_length]; omega)
    · exact regionL_cons _ (hR i hi)
  · have := hm0 j (by rw [eqChain_length]; omega)
    simpa [eqChain, word_one] using this

/-- **The public input's chain's loop, complete, placed**: from `g`, over the chain `piW` at `g^b`
and the point's complements `ps` at `g^bp`. -/
theorem l15_kid_complete (κ : ℕ) {b bp m : ℕ} {rm glm : E} {ps : List E} {L : Main.Layout}
    (hm2 : 2 ≤ m) (hglm : glm = gen ^ m) (hps : m ≤ ps.length)
    (hrd : ∀ rd, LowDef κ rd → MemL rd L → ReadsAt rd (ofK (gpow bp)) ps)
    (hR : ∀ i, bp ≤ i ∧ i < bp + m → RegionL L i) :
    CompleteAtD fs cert κ "__loop15" ((b, piW rm ps m) :: L)
      [word 2 0 0, glm, ofK (gpow b), ofK (gpow bp)] (Returns []) := by
  refine Lift.completeAtD_of_relIn l15_pure List.mem_cons_self fun rd hl hm => ?_
  have hm0 : ReadsAt rd (ofK (gpow b)) (piW rm ps m) := hm _ List.mem_cons_self
  have hmL : MemL rd L := fun q hq => hm q (List.mem_cons_of_mem _ hq)
  have hstep : ∀ k, 1 ≤ k → k < m →
      (piW rm ps m).getD (k + 1) 0 = (piW rm ps m).getD k 0 * (ps.take m).getD k 0 := by
    intro k hk1 hkm
    have e : (ps.take m).getD k 0 = ps.getD k 0 := by
      simp [List.getD_eq_getElem?_getD, hkm]
    rw [piW_getD (by omega), piW_getD (by omega), ite_neg' (by omega), ite_neg' (by omega),
      prod_Ico_succ_top (by omega), e, mul_assoc]
  have h := l15_relIn (piW_length rm ps m) (by simp; omega) hm0 (readsAt_take (hrd rd hl hmL) m) hstep
    (R := RegionL ((b, piW rm ps m) :: L)) (fun i hi => by
      rcases hi with hi | hi
      · exact regionL_head hi.1 (by rw [piW_length]; omega)
      · exact regionL_cons _ (hR i hi)) (m - 2) 1 (by omega) le_rfl
  rw [← hglm, pow_one, ← word_gen] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **The terminal's callees are complete, placed**, on the honest data. -/
theorem termKids_complete (κ : ℕ) (hκ : 6 ≤ κ) (Lin : Main.Layout) (D : TermData) (b0 : ℕ)
    (hreg : ∀ i, TermRegion D.B D.zs.length D.chis.length D.τ i → RegionL Lin i)
    (hzl : D.zs.length ≤ 34) (hcl : D.chis.length ≤ 34) (hxl : D.x.length ≤ 28)
    (hτ : D.τ + 6 ≤ 34) (hol : D.outPt.length = D.τ + 6) (hrl : D.ringPoint.length = D.τ + 6)
    (hcf : D.coeffs.length = 64) (hgmu : D.gmu = gen ^ D.zs.length)
    (hgz : D.gzcn = gen ^ D.chis.length) (hglm : D.glm = gen ^ D.m) (hgtau : D.gtau = gen ^ D.τ)
    (hm1 : 1 ≤ D.m) (hm : D.m ≤ 32) (hKC : ∀ c < Tables.nCommittedCols, D.KC.getD c 0 < 29)
    (hOF : ∀ c < Tables.nCommittedCols, D.OF.getD c 0 < 2 ^ 28 ∧ 2 ^ D.KC.getD c 0 ∣ D.OF.getD c 0)
    (hrd : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd (ofK (gpow D.B.zeta)) D.zs ∧
      ReadsAt rd (ofK (gpow D.B.chi)) D.chis ∧ ReadsAt rd (ofK (gpow D.B.zv)) D.outPt ∧
      ReadsAt rd (ofK (gpow D.B.pt1)) (p1Of D.x)) :
    ∀ k ∈ termKids Lin D b0, ∀ pv, (k pv).taken = true →
      CompleteAtD fs cert κ (k pv).f (k pv).Lin (k pv).args (k pv).Out := by
  have hpl : (p1Of D.x).length = 40 := p1Of_length (by simp only [termPointCap]; omega)
  have hpt : (padPoint D.x).length = 40 := padPoint_length (by simp only [termPointCap]; omega)
  have hw64 : word 64 0 0 = gen ^ 6 := word_two_pow (a := 6) (by decide)
  intro k hk pv ht
  simp only [termKids, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hk
  rcases hk with ((rfl | rfl | rfl | rfl) | ⟨c, hc, rfl⟩) | rfl | rfl
  · exact eqc_kid_complete κ hκ (by omega) (by simp; omega) hgmu
      (fun rd hl hm => ⟨(hrd rd hl hm).1, readsAt_take (hrd rd hl hm).2.2.2 _⟩)
      (fun i hi => hreg i (by
        rcases hi with hi | hi
        · exact Or.inl hi
        · simp only [TermRegion]; omega))
  · exact eqc_kid_complete κ hκ (by omega) (by simp; omega) hgz
      (fun rd hl hm => ⟨(hrd rd hl hm).2.1, readsAt_take (hrd rd hl hm).2.2.2 _⟩)
      (fun i hi => hreg i (by simp only [TermRegion]; omega))
  · have hne : word 2 0 0 + D.glm ≠ 0 := by simpa using ht
    have hm2 : 2 ≤ D.m := by
      by_contra h
      apply hne
      rw [hglm, show D.m = 1 by omega, word_gen, pow_one]
      exact e_add_self _
    exact l15_kid_complete κ hm2 hglm (by omega) (fun rd hl hm => (hrd rd hl hm).2.2.2)
      (fun i hi => hreg i (by simp only [TermRegion]; omega))
  · exact Tables.selector_tables_completeAt fs cert κ _ _ _ _ (by simp [pt28]; omega)
      (by simp [pt128]; omega)
  · have hst : Tables.stOut D.B.pt D.B.pt1 (pt28 D.x) (pt128 D.x) (stRes pv).1 (stRes pv).2 :=
      @of_decide_eq_true _ (Classical.propDecidable _) ht
    obtain ⟨ese, esg, h1, h2⟩ := hst
    have hL : (selKid D c pv).Lin = Tables.stOwn D.B.pt D.B.pt1 ese esg (pt28 D.x) (pt128 D.x) ++
        Tables.stLin D.B.pt D.B.pt1 (pt28 D.x) (pt128 D.x) := by
      show @ite _ _ (Classical.propDecidable _) _ _ = _
      rw [@ite_pos' _ _ (Classical.propDecidable _) _ _ ⟨ese, esg, h1, h2⟩, h2]
    have ha : (selKid D c pv).args = [gen ^ D.OF.getD c 0, ofK (gpow ese), ofK (gpow esg)] := by
      show [_, (stRes pv).1.getD 0 0, (stRes pv).1.getD 1 0] = _
      rw [h1]; rfl
    rw [hL, ha]
    exact cs_completeAt κ (hKC c hc) (hOF c hc).1 (hOF c hc).2 (by simp [pt28]; omega)
      (by simp [pt128]; omega)
  · have e : D.gtau * word 64 0 0 = gen ^ D.outPt.length := by rw [hgtau, hw64, ← pow_add, hol]
    show CompleteAtD fs cert κ "eq_prefix_chain" _
      [ofK (gpow (b0 + 105)), word 1 0 0, ofK (gpow D.B.zv), ofK (gpow D.B.pt1), D.gtau * word 64 0 0]
      (Returns [])
    exact eqc_kid_complete κ hκ (by omega) (by simp; omega) e
      (fun rd hl hm => ⟨(hrd rd hl hm).2.2.1, readsAt_take (hrd rd hl hm).2.2.2 _⟩)
      (fun i hi => hreg i (by simp only [TermRegion]; omega))
  · have e1 : ofK (gpow D.B.zv) * word 549755813888 0 0 = ofK (gpow (D.B.zv + 39)) := by
      rw [show (549755813888 : ℕ) = 2 ^ 39 by norm_num, word_two_pow (by decide), ofK_gpow_mul_gen]
    have e2 : D.gtau * word 64 0 0 = gen ^ (D.τ + 6) := by rw [hgtau, hw64, ← pow_add]
    show CompleteAtD fs cert κ "ring_switch_weight" _
      [ofK (gpow D.B.zv) * word 549755813888 0 0, ofK (gpow D.B.pt1), ofK (gpow D.B.ct),
        D.gtau * word 64 0 0] _
    rw [e1, e2]
    exact rsw_completeAt κ (by omega) hrl (by simp; omega) hcf

end
end LeanVM.Guest.B1.VerifySub
