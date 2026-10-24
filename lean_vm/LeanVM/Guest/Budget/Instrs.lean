/-
  LeanVM.Guest.Budget.Instrs

  `main`'s instruction bound (`mainCount`) at the honest counts within a budget linear in the
  node's work (`mainInstrs`).
-/

module

public import LeanVM.Guest.Budget.MainCount
public import LeanVM.Guest.B1.Main.MainWords

/-!
# The instruction budget

`mainInstrs H fs SB SK Bv jt`: per unit of work, `mainCount`'s terms at B1-f's linear words
bounds (`clB_le`, `hDvB_le`, `l5B_le`), each ratio `α · B / 1000` rounded up term by term
(`div_aff3`): a constant, `main`'s static callees, the claim lists' ratio per declared claim, the
loops per coverage slot and raw signature, `da_verify`'s ratio per direct blob and row, the
children's loop's ratio and `aggregate_claims` per child, and the loop's ratio per child's claim.
`mainCount_le`: on the honest run within the limits, `mainCount` plus `jt` is at most it.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (Linear work)
open LeanVM.Guest.B1.Main (hm mainBsH clC dvC dvS l5A0 l5A1 l5A2 clB_le hDvB_le l5B_le coverage_eq
  xPlan sPlan dPlan)

@[expose] public section

/-- A ratio of an affine bound in two units, rounded up term by term. -/
theorem div_aff3 (α a b c n y : ℕ) :
    α * (a + n * b + c * y) / 1000 ≤
      (α * a / 1000 + 1) + n * (α * b / 1000 + 1) + y * (α * c / 1000 + 1) := by
  apply Nat.div_le_of_le_mul
  have ha := Nat.lt_div_mul_add (a := α * a) (b := 1000) (by norm_num)
  have hb := Nat.lt_div_mul_add (a := α * b) (b := 1000) (by norm_num)
  have hc := Nat.lt_div_mul_add (a := α * c) (b := 1000) (by norm_num)
  have e : α * (a + n * b + c * y) = α * a + n * (α * b) + y * (α * c) := by ring
  rw [e]
  have h2 : n * (α * b) ≤ n * (α * b / 1000 * 1000 + 1000) := Nat.mul_le_mul_left _ (by omega)
  have h3 : y * (α * c) ≤ y * (α * c / 1000 * 1000 + 1000) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

variable {ω fs : String → ℕ}

/-- **The instruction budget** at `ω`: `mainCount`'s terms, linearly in the work. -/
def mainInstrs (H : MainCounts ω fs) (SB SK : String → ℕ) (Bv jt : ℕ) : Linear where
  base := ω "main" + H.kExp + H.kDl + H.kSd + jt + 2 * (H.αcl * clC fs SB / 1000 + 1)
  declared := H.αcl * (13 + SK "__loop16") / 1000 + 1
  coverage := H.kL0 + H.kL1 + H.kL2
  rawXmss := H.kL3
  rawSphincs := H.kL4
  rawDa := H.αdv * dvC fs SB / 1000 + 1 + H.kCov
  rawDaRows := H.αdv * dvS SB SK / 1000 + 1
  children := (H.α5 * l5A0 fs / 1000 + 1) + (H.α5 * (l5A1 fs SB + Bv) / 1000 + 1) + H.aggC +
    H.aggD
  childClaims := H.α5 * l5A2 fs / 1000 + 1

set_option maxHeartbeats 1000000 in
/-- **`main`'s instruction bound within the budget** on the honest run within the limits. -/
theorem mainCount_le (H : MainCounts ω fs) (SB SK : String → ℕ) (Bv jt : ℕ) {bytecode : List K}
    {seed : Digest} {s : NodeStatement} {w : NodeWitness} (hr : NodeRel bytecode seed s w)
    (hl : Limits bytecode s w) :
    mainCount H (hm fs 0 seed s w) (mainBsH fs SB SK Bv s w) + jt ≤
      (mainInstrs H SB SK Bv jt).eval (work s w) := by
  have hX := clB_le fs SB SK s.claims.xmss.length
  have hS := clB_le fs SB SK s.claims.sphincs.length
  have hD := hDvB_le fs SB SK hr hl
  have hcov := coverage_eq (s := s) (w := w)
  simp only [List.length_append] at hcov
  have hd : (hm fs 0 seed s w).nd ≤ 1 := hl.directDa
  have hncb : (hm fs 0 seed s w).nc ≤ 16 := hl.children
  -- the ratios at the linear bounds
  have rX : H.αcl * (mainBsH fs SB SK Bv s w).Bx / 1000 ≤ (H.αcl * clC fs SB / 1000 + 1) +
      s.claims.xmss.length * (H.αcl * (13 + SK "__loop16") / 1000 + 1) := by
    have := div_aff3 H.αcl (clC fs SB) (13 + SK "__loop16") 0 s.claims.xmss.length 0
    simp only [Nat.zero_mul, Nat.add_zero, Nat.mul_zero] at this
    exact le_trans (Nat.div_le_div_right (Nat.mul_le_mul_left _ hX)) this
  have rS : H.αcl * (mainBsH fs SB SK Bv s w).Bs / 1000 ≤ (H.αcl * clC fs SB / 1000 + 1) +
      s.claims.sphincs.length * (H.αcl * (13 + SK "__loop16") / 1000 + 1) := by
    have := div_aff3 H.αcl (clC fs SB) (13 + SK "__loop16") 0 s.claims.sphincs.length 0
    simp only [Nat.zero_mul, Nat.add_zero, Nat.mul_zero] at this
    exact le_trans (Nat.div_le_div_right (Nat.mul_le_mul_left _ hS)) this
  have hdecl : s.claims.xmss.length + s.claims.sphincs.length ≤ (work s w).declared := by
    simp only [work]; omega
  have hcov' : coverage s w = (work s w).coverage := rfl
  have e0 : (hm fs 0 seed s w).nda + (hm fs 0 seed s w).ndd =
      s.claims.da.length + (dPlan s w).dups.length := rfl
  have e1 : (hm fs 0 seed s w).nxd = (xPlan s w).dups.length := rfl
  have e2 : (hm fs 0 seed s w).nsd = (sPlan s w).dups.length := rfl
  have e3 : (hm fs 0 seed s w).nrx = (work s w).rawXmss := rfl
  have e4 : (hm fs 0 seed s w).nrs = (work s w).rawSphincs := rfl
  have e5 : (hm fs 0 seed s w).nc = (work s w).children := rfl
  have e6 : (hm fs 0 seed s w).nd = (work s w).rawDa := rfl
  have c0 : ((hm fs 0 seed s w).nda + (hm fs 0 seed s w).ndd) * H.kL0 ≤
      H.kL0 * (work s w).coverage := by
    rw [e0, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have c1 : (hm fs 0 seed s w).nxd * H.kL1 ≤ H.kL1 * (work s w).coverage := by
    rw [e1, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have c2 : (hm fs 0 seed s w).nsd * H.kL2 ≤ H.kL2 * (work s w).coverage := by
    rw [e2, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have cX : s.claims.xmss.length * (H.αcl * (13 + SK "__loop16") / 1000 + 1) +
      s.claims.sphincs.length * (H.αcl * (13 + SK "__loop16") / 1000 + 1) ≤
      (H.αcl * (13 + SK "__loop16") / 1000 + 1) * (work s w).declared := by
    rw [← Nat.add_mul, Nat.mul_comm]; exact Nat.mul_le_mul_left _ hdecl
  unfold mainCount
  simp only [Linear.eval, mainInstrs]
  rw [e3, e4]
  have r3 : (work s w).rawXmss * H.kL3 = H.kL3 * (work s w).rawXmss := Nat.mul_comm _ _
  have r4 : (work s w).rawSphincs * H.kL4 = H.kL4 * (work s w).rawSphincs := Nat.mul_comm _ _
  have r5 : (work s w).rawDaRows * (H.αdv * dvS SB SK / 1000 + 1) =
      (H.αdv * dvS SB SK / 1000 + 1) * (work s w).rawDaRows := Nat.mul_comm _ _
  -- the direct blob
  have hDa : (if (hm fs 0 seed s w).nd = 1 then
      H.αdv * (mainBsH fs SB SK Bv s w).Bd / 1000 + H.kCov else 0) ≤
      (H.αdv * dvC fs SB / 1000 + 1 + H.kCov) * (work s w).rawDa +
        (H.αdv * dvS SB SK / 1000 + 1) * (work s w).rawDaRows := by
    split_ifs with h1
    · have hra : (work s w).rawDa = 1 := by rw [← e6, h1]
      have hD1 : (mainBsH fs SB SK Bv s w).Bd ≤ dvC fs SB + (work s w).rawDaRows * dvS SB SK := by
        have := hD; rw [hra, Nat.one_mul] at this; exact this
      have rD : H.αdv * (mainBsH fs SB SK Bv s w).Bd / 1000 ≤ (H.αdv * dvC fs SB / 1000 + 1) +
          (work s w).rawDaRows * (H.αdv * dvS SB SK / 1000 + 1) := by
        have := div_aff3 H.αdv (dvC fs SB) (dvS SB SK) 0 (work s w).rawDaRows 0
        simp only [Nat.zero_mul, Nat.add_zero, Nat.mul_zero] at this
        exact le_trans (Nat.div_le_div_right (Nat.mul_le_mul_left _ hD1)) this
      rw [hra]; omega
    · omega
  -- the children
  have hCh : (if (hm fs 0 seed s w).nc = 0 then 0 else
      H.α5 * (mainBsH fs SB SK Bv s w).B5 / 1000 + (H.aggC + H.aggD * (hm fs 0 seed s w).nc)) ≤
      ((H.α5 * l5A0 fs / 1000 + 1) + (H.α5 * (l5A1 fs SB + Bv) / 1000 + 1) + H.aggC + H.aggD) *
        (work s w).children + (H.α5 * l5A2 fs / 1000 + 1) * (work s w).childClaims := by
    split_ifs with h0
    · omega
    · have h5 : (mainBsH fs SB SK Bv s w).B5 ≤ l5A0 fs + w.children.length * (l5A1 fs SB + Bv) +
          l5A2 fs * (work s w).childClaims := l5B_le fs SB Bv s w h0
      have r5' := le_trans (Nat.div_le_div_right (c := 1000) (Nat.mul_le_mul_left H.α5 h5))
        (div_aff3 H.α5 (l5A0 fs) (l5A1 fs SB + Bv) (l5A2 fs) w.children.length
          (work s w).childClaims)
      have hn1 : 1 ≤ w.children.length := Nat.pos_of_ne_zero h0
      have e5' : w.children.length = (work s w).children := rfl
      rw [e5'] at r5' hn1
      rw [e5]
      have : (H.α5 * l5A0 fs / 1000 + 1) ≤ (H.α5 * l5A0 fs / 1000 + 1) * (work s w).children :=
        Nat.le_mul_of_pos_right _ hn1
      have : H.aggC ≤ H.aggC * (work s w).children := Nat.le_mul_of_pos_right _ hn1
      have e7 : ((H.α5 * l5A0 fs / 1000 + 1) + (H.α5 * (l5A1 fs SB + Bv) / 1000 + 1) + H.aggC +
          H.aggD) * (work s w).children = (H.α5 * l5A0 fs / 1000 + 1) * (work s w).children +
          (work s w).children * (H.α5 * (l5A1 fs SB + Bv) / 1000 + 1) +
          H.aggC * (work s w).children + H.aggD * (work s w).children := by ring
      have e8 : (H.α5 * l5A2 fs / 1000 + 1) * (work s w).childClaims =
          (work s w).childClaims * (H.α5 * l5A2 fs / 1000 + 1) := Nat.mul_comm _ _
      omega
  have ecov : (H.kL0 + H.kL1 + H.kL2) * (work s w).coverage = H.kL0 * (work s w).coverage +
      H.kL1 * (work s w).coverage + H.kL2 * (work s w).coverage := by ring
  omega

end
end LeanVM.Guest.Budget
