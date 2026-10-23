/-
  LeanVM.Guest.B1.Tables.VtC.ZInBuf

  Where `verify_tables`' statements `5152 ..< 5259` and `10209 ..< 10251` load: `dims_g`, the
  rounds' records, the running products, `claim_pool`.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZTail
public import LeanVM.Guest.B1.Tables.VtC.InBuf

/-!
# The loads, inside buffers

`vtZ_inBuf`: the loads of `5152 ..< 5259` read `dims_g` (`7` words), the records (`7(n + 1)`
words at `w 5912`, the last one `7n` on) and the running products (`n + 1` at `w 5915`).
`vtZt_inBuf`: those of `10209 ..< 10251` read `claim_pool` (`165` words).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The loads of `5152 ..< 5259`** read `dims_g`, the records and the running products. -/
theorem vtZ_inBuf {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 22) {n : ℕ}
    (hwn : w 5817 = gen ^ n) {bufs : List (E × ℕ)} (b10 : (vtσ rd w args (.n 10), 7) ∈ bufs)
    (bR : (w 5912, 7 * (n + 1)) ∈ bufs) (bC : (w 5915, n + 1) ∈ bufs) :
    LoadsInBuf (vtσ rd w args) bufs ((vtPre.drop 5152).take 107) := by
  have g0 := vt_goodL (rd := rd) (w := w) hl 5152
    [.atom (.hint (.witness "zc_tau_max" (.stack [.n 5817])))] (by decide +kernel)
  have g1 := vt_goodL (rd := rd) (w := w) hl 5223 [.atom (.hint (.allocDyn (.n 5912) (.n 5911)))]
    (by decide +kernel)
  have g2 := vt_goodL (rd := rd) (w := w) hl 5226 [.atom (.hint (.allocDyn (.n 5915) (.n 5914)))]
    (by decide +kernel)
  have g3 := vt_goodL (rd := rd) (w := w) hl 5242 [.atom (.mul (.n 5922) (.n 5817) (.n 5817)),
    .atom (.mul (.n 5923) (.n 5922) (.n 5817)), .atom (.mul (.n 5924) (.n 5923) (.n 5923)),
    .atom (.mul (.n 5925) (.n 5924) (.n 5817)), .atom (.mul (.n 5926) (.n 5912) (.n 5925))]
    (by decide +kernel)
  have e := tbStmtsEqb_sound zBlk_at
  have hlen107 : zBlk.length = 107 := rfl
  rw [← hlen107, ← e]
  generalize vtσ rd w args = σ at *
  simp only [GoodL, GoodS, Good, fixNe, List.forall_mem_cons, Nat.reduceLT, and_true,
    ↓reduceIte] at g0 g1 g2 g3
  obtain ⟨m22, m23, m24, m25, m26⟩ := g3
  have v5912 : σ (.n 5912) = w 5912 := g1
  have v5926 : σ (.n 5926) = w 5912 * gen ^ (7 * n) := by
    rw [m26, m25, m24, m23, m22, g0.1, hwn, v5912]; ring
  intro d p off hm
  simp only [zBlk, List.mem_cons, Stmt.atom.injEq, Atom.load.injEq, reduceCtorEq, false_or,
    or_false, List.not_mem_nil] at hm
  have hR : ∀ k < 7, InBuf σ bufs (.n 5912) k := fun k hk => ⟨_, bR, 0, by rw [v5912]; simp,
    by omega⟩
  have hN : ∀ k < 7, InBuf σ bufs (.n 5926) k := fun k hk => ⟨_, bR, 7 * n, v5926, by omega⟩
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals first
    | exact vt_inBuf_direct b10 (by norm_num)
    | exact hR _ (by norm_num)
    | exact hN _ (by norm_num)
    | exact ⟨_, bC, 0, by rw [g2]; simp, by omega⟩

set_option maxRecDepth 100000 in
/-- **The loads of `10209 ..< 10251`** read `claim_pool`. -/
theorem vtZt_inBuf {rd : Reader} {w : ℕ → E} {args : List E} {bufs : List (E × ℕ)}
    (b16 : (vtσ rd w args (.n 16), 165) ∈ bufs) :
    LoadsInBuf (vtσ rd w args) bufs ((vtPre.drop 10209).take 42) := by
  have e := tbStmtsEqb_sound zTail_at
  have hlen42 : zTail.length = 42 := rfl
  rw [← hlen42, ← e]
  intro d p off hm
  simp only [zTail, List.mem_cons, Stmt.atom.injEq, Atom.load.injEq, reduceCtorEq, false_or,
    or_false, List.not_mem_nil] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact vt_inBuf_direct b16 (by norm_num)

end
end LeanVM.Guest.B1.Tables
