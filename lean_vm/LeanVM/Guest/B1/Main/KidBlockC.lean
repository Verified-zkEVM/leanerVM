/-
  LeanVM.Guest.B1.Main.KidBlockC

  `__loop4`'s block (a child) on its honest valuation: the block evaluated (`Fwd.ev`) on the
  loop's words, the hints and the calls' returns the honest ones; its atoms hold and its words.
-/

module

public import LeanVM.Guest.B1.Main.KidCChk
public import LeanVM.Guest.B1.Da.VerifyL23Complete
public import LeanVM.Guest.B1.Digest.Range
public import LeanVM.Guest.B1.Digest.ClaimListCLast
public import LeanVM.Guest.B1.Da.AtBase

/-!
# A child's block, completely

`l5W`: the oracle of the block's hints and calls' returns (the counts `g^ex`, `g^es`, the two
claim lists' digests, the statement's digest). `l5_core`: on a memory defined below `2^16`
holding `written[x]`, the child's DA digest's two cells at `da_digests·x²`, the statement's
digest at `child_pi_table·x²` and `written[x·g]`, every atom of the block holds on `l5σ`, with
its words (`L5Vals`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Da (good_mul good_load)
open LeanVM.Guest.B1 (LowDef)

@[expose] public section

/-- The oracle of `__loop4`'s block. -/
def l5W (ex es : ℕ) (cx0 cx1 cs0 cs1 p0 p1 : E) (j : ℕ) : E :=
  if j = 18 then gen ^ ex else if j = 19 then gen ^ es else if j = 30 then cx0
  else if j = 31 then cx1 else if j = 33 then cs0 else if j = 34 then cs1
  else if j = 45 then p0 else if j = 46 then p1
  else 0

/-- `__loop4`'s body. -/
def l5Body : List Stmt := l5Pre ++ [l5Tail, .ret []]

/-- `__loop4`'s honest valuation. -/
noncomputable def l5σ (rd : Reader) (args : List E) (w : ℕ → E) : Val :=
  B1.Val.ofArgs (ev rd w args l5Body)

/-- **The words of a child's block.** -/
structure L5Vals (rd : Reader) (σ : Val) (args : List E) (c ex es : ℕ)
    (base cx0 cx1 cs0 cs1 d0 d1 p0 p1 : E) : Prop where
  atoms : ∀ a ∈ atomsIn l5Pre, a.Holds rd σ
  par : ∀ i < 16, σ (.n i) = args.getD i 0
  v16 : σ (.n 16) = args.getD 2 0 * gen ^ c
  v17 : σ (.n 17) = base
  v18 : σ (.n 18) = gen ^ ex
  v19 : σ (.n 19) = gen ^ es
  v28 : σ (.n 28) = gen ^ ex * gen ^ es
  v29 : σ (.n 29) = 1
  v30 : σ (.n 30) = cx0
  v31 : σ (.n 31) = cx1
  v32 : σ (.n 32) = base * gen ^ ex
  v33 : σ (.n 33) = cs0
  v34 : σ (.n 34) = cs1
  v40 : σ (.n 40) = args.getD 8 0 * gen ^ (24 * c)
  v42 : σ (.n 42) = args.getD 9 0 * (gen ^ c * gen ^ c)
  v43 : σ (.n 43) = d0
  v44 : σ (.n 44) = d1
  v45 : σ (.n 45) = p0
  v46 : σ (.n 46) = p1
  v48 : σ (.n 48) = args.getD 12 0 * (gen ^ c * gen ^ c)
  v49 : σ (.n 49) = args.getD 12 0 * (gen ^ c * gen ^ c)
  v55 : σ (.n 55) = args.getD 15 0 * gen ^ (24 * c)
  v57 : σ (.n 57) = args.getD 2 0 * gen ^ c
  v60 : σ (.n 60) = gen ^ (c + 1) + args.getD 1 0
  v62 : σ (.n 62) = gen ^ (c + 1)

theorem gen_pow_mul_inv {K e : ℕ} (h : e ≤ K) : gen ^ K * (gen ^ e)⁻¹ = gen ^ (K - e) := by
  have hg : gen ^ e ≠ 0 := pow_ne_zero _ gen_ne_zero
  rw [show K = (K - e) + e by omega, pow_add, mul_assoc, mul_inv_cancel₀ hg, mul_one,
    Nat.add_sub_cancel]

theorem low_load {rd : Reader} (hlow : LowDef 16 rd) {e : ℕ} (he : e < 2 ^ 16) :
    LoadHolds rd (gen ^ e) 0 (rdAt rd (gen ^ e) 0) := by
  have := B1.loadHolds_low hlow he
  rw [← gen_pow_eq_ofK] at this
  rw [rdAt, show (gen ^ e).limb 0 * gpow 0 = gpow e by
    rw [Da.limb0_gen_pow_mul, Nat.add_zero]]
  exact this

set_option maxRecDepth 20000 in
/-- **A child's block holds** on its honest valuation. -/
theorem l5_core {rd : Reader} (hlow : LowDef 16 rd) {c : ℕ}
    {N written lxt cover lxs lst lss carried dadig s0 s1 cpi glp gsq cfresh : E}
    {ex es : ℕ} {base cx0 cx1 cs0 cs1 d0 d1 p0 p1 : E}
    (hex : ex ≤ 65535) (hes : es ≤ 65535)
    (hbase : LoadHolds rd (written * gen ^ c) 0 base)
    (hda0 : LoadHolds rd (dadig * (gen ^ c * gen ^ c)) 0 d0)
    (hda1 : LoadHolds rd (dadig * (gen ^ c * gen ^ c)) 1 d1)
    (hpi0 : LoadHolds rd (cpi * (gen ^ c * gen ^ c)) 0 p0)
    (hpi1 : LoadHolds rd (cpi * (gen ^ c * gen ^ c)) 1 p1)
    (hnext : LoadHolds rd (written * gen ^ c) 1 (base * (gen ^ ex * gen ^ es))) :
    L5Vals rd (l5σ rd [gen ^ c, N, written, lxt, cover, lxs, lst, lss, carried, dadig,
        s0, s1, cpi, glp, gsq, cfresh] (l5W ex es cx0 cx1 cs0 cs1 p0 p1))
      [gen ^ c, N, written, lxt, cover, lxs, lst, lss, carried, dadig,
        s0, s1, cpi, glp, gsq, cfresh] c ex es base cx0 cx1 cs0 cs1 d0 d1 p0 p1 := by
  have hok := l5c_ok
  unfold l5COk at hok
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨c', hchk⟩, hst⟩, hcanA⟩, hneeds⟩, hcalls⟩ := hok
  set args : List E := [gen ^ c, N, written, lxt, cover, lxs, lst, lss, carried, dadig,
    s0, s1, cpi, glp, gsq, cfresh] with hargs
  set w := l5W ex es cx0 cx1 cs0 cs1 p0 p1 with hw
  set σ := l5σ rd args w with hσ
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd w l5Body args hchk
  rw [show args.length = 16 from rfl, show l5Body = l5Pre ++ [l5Tail, .ret []] from rfl, hst] at hgs
  have hg : ∀ a ∈ atomsIn l5Pre, Good rd l5S w σ a := fun a ha =>
    hgs (.atom a) (List.mem_append_left _ (Da.atom_mem_of_atomsIn ha))
  have par : ∀ i < 16, σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd w (l := args) hchk (by simpa [hargs] using hi)
  have hmem : ∀ a : Atom, decide (a ∈ atomsIn l5Pre) = true → Good rd l5S w σ a :=
    fun a ha => hg a (of_decide_eq_true ha)
  have gconst : ∀ {k : ℕ} (hk : k < l5Pre.length), GoodS rd l5S w σ l5Pre[k] :=
    fun hk => hgs _ (List.mem_append_left _ (List.getElem_mem hk))
  -- the words
  have e0 : σ (.n 0) = gen ^ c := par 0 (by omega)
  have p2 : σ (.n 2) = written := par 2 (by omega)
  have p9 : σ (.n 9) = dadig := par 9 (by omega)
  have p12 : σ (.n 12) = cpi := par 12 (by omega)
  have mul' : ∀ {d x y : ℕ}, x < d → y < d → decide (Atom.mul (.n d) (.n x) (.n y) ∈ atomsIn l5Pre) = true →
      σ (.n d) = σ (.n x) * σ (.n y) := fun hx hy h => good_mul hx hy (hmem _ h)
  have v16 : σ (.n 16) = written * gen ^ c := by
    rw [mul' (d := 16) (x := 2) (y := 0) (by omega) (by omega) (by decide +kernel), p2, e0]
  have hS17 : Atom.load (.n 17) (.n 16) 0 ∉ l5S := by decide
  have v17 : σ (.n 17) = base := by
    rw [good_load hS17 (hmem _ (by decide +kernel)), v16, rdAt_of_load hbase]
  have hmeta := hmem (.hint (.witness "child_meta" (.stack [.n 18, .n 19]))) (by decide +kernel)
  have v18 : σ (.n 18) = gen ^ ex := hmeta (.n 18) (by simp)
  have v19 : σ (.n 19) = gen ^ es := hmeta (.n 19) (by simp)
  have v28 : σ (.n 28) = gen ^ ex * gen ^ es := by
    rw [mul' (d := 28) (x := 18) (y := 19) (by omega) (by omega) (by decide +kernel), v18, v19]
  have v29 : σ (.n 29) = 1 := by
    rw [show σ (.n 29) = word 1 0 0 from gconst (k := 8) (by decide), word_one]
  have hcall : ∀ s ∈ l5Calls, GoodS rd l5S w σ s := by
    intro s hs
    obtain ⟨t, ht, he⟩ := List.any_eq_true.mp (hcalls s hs)
    rw [← stmtEqb_sound he]
    exact hgs t (List.mem_append_left _ ht)
  simp only [l5Calls, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    GoodS] at hcall
  obtain ⟨hcx, hcs, hsd⟩ := hcall
  have v30 : σ (.n 30) = cx0 := hcx.1
  have v31 : σ (.n 31) = cx1 := hcx.2
  have v33 : σ (.n 33) = cs0 := hcs.1
  have v34 : σ (.n 34) = cs1 := hcs.2
  have v45 : σ (.n 45) = p0 := hsd.1
  have v46 : σ (.n 46) = p1 := hsd.2
  have v32 : σ (.n 32) = base * gen ^ ex := by
    rw [mul' (d := 32) (x := 17) (y := 18) (by omega) (by omega) (by decide +kernel), v17, v18]
  have v35 := mul' (d := 35) (x := 0) (y := 0) (by omega) (by omega) (by decide +kernel)
  have v36 := mul' (d := 36) (x := 35) (y := 0) (by omega) (by omega) (by decide +kernel)
  have v37 := mul' (d := 37) (x := 36) (y := 36) (by omega) (by omega) (by decide +kernel)
  have v38 := mul' (d := 38) (x := 37) (y := 37) (by omega) (by omega) (by decide +kernel)
  have v39 := mul' (d := 39) (x := 38) (y := 38) (by omega) (by omega) (by decide +kernel)
  have v40' := mul' (d := 40) (x := 8) (y := 39) (by omega) (by omega) (by decide +kernel)
  have v41 := mul' (d := 41) (x := 0) (y := 0) (by omega) (by omega) (by decide +kernel)
  have v42' := mul' (d := 42) (x := 9) (y := 41) (by omega) (by omega) (by decide +kernel)
  have v47 := mul' (d := 47) (x := 0) (y := 0) (by omega) (by omega) (by decide +kernel)
  have v48' := mul' (d := 48) (x := 12) (y := 47) (by omega) (by omega) (by decide +kernel)
  have v49' := mul' (d := 49) (x := 12) (y := 47) (by omega) (by omega) (by decide +kernel)
  have v50 := mul' (d := 50) (x := 0) (y := 0) (by omega) (by omega) (by decide +kernel)
  have v51 := mul' (d := 51) (x := 50) (y := 0) (by omega) (by omega) (by decide +kernel)
  have v52 := mul' (d := 52) (x := 51) (y := 51) (by omega) (by omega) (by decide +kernel)
  have v53 := mul' (d := 53) (x := 52) (y := 52) (by omega) (by omega) (by decide +kernel)
  have v54 := mul' (d := 54) (x := 53) (y := 53) (by omega) (by omega) (by decide +kernel)
  have v55' := mul' (d := 55) (x := 15) (y := 54) (by omega) (by omega) (by decide +kernel)
  have v56 := mul' (d := 56) (x := 17) (y := 28) (by omega) (by omega) (by decide +kernel)
  have v57' := mul' (d := 57) (x := 2) (y := 0) (by omega) (by omega) (by decide +kernel)
  have v59 := mul' (d := 59) (x := 0) (y := 58) (by omega) (by omega) (by decide +kernel)
  have v62' := mul' (d := 62) (x := 0) (y := 61) (by omega) (by omega) (by decide +kernel)
  have v58 : σ (.n 58) = word 2 0 0 := gconst (k := 40) (by decide)
  have v61 : σ (.n 61) = word 2 0 0 := gconst (k := 43) (by decide)
  have v60 : σ (.n 60) = σ (.n 59) + σ (.n 1) := hmem (.add (.n 60) (.n 59) (.n 1)) (by decide +kernel)
  have h24 : σ (.n 39) = gen ^ (24 * c) := by
    rw [v39, v38, v37, v36, v35, e0, mul_comm 24 c, pow_mul]; ring
  have h54 : σ (.n 54) = gen ^ (24 * c) := by
    rw [v54, v53, v52, v51, v50, e0, mul_comm 24 c, pow_mul]; ring
  have v42 : σ (.n 42) = dadig * (gen ^ c * gen ^ c) := by rw [v42', v41, p9, e0]
  have hS43 : Atom.load (.n 43) (.n 42) 0 ∉ l5S := by decide
  have hS44 : Atom.load (.n 44) (.n 42) 1 ∉ l5S := by decide
  have v43 : σ (.n 43) = d0 := by
    rw [good_load hS43 (hmem _ (by decide +kernel)), v42, rdAt_of_load hda0]
  have v44 : σ (.n 44) = d1 := by
    rw [good_load hS44 (hmem _ (by decide +kernel)), v42, rdAt_of_load hda1]
  -- the range checks
  have hrc : ∀ {x y t1 t2 k : ℕ} {e K : ℕ}, k < y → e ≤ K → K < 2 ^ 16 →
      decide (Atom.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n k) ∈ atomsIn l5Pre) = true →
      σ (.n x) = gen ^ e → σ (.n k) = gen ^ K →
      (Atom.rangeCheck (.n x) (.n y) (.n t1) (.n t2) (.n k)).Holds rd σ := by
    intro x y t1 t2 k e K hky heK hK h hx hk
    have hg' := hmem _ h
    simp only [Good] at hg'
    rw [ite_pos' hky] at hg'
    obtain ⟨g1, g2, g3⟩ := hg'
    have hy : σ (.n y) = gen ^ (K - e) := by rw [g3, hk, hx, gen_pow_mul_inv heK]
    refine ⟨?_, ?_, ?_⟩
    · rw [g1, hx]; exact low_load hlow (by omega)
    · rw [hk, hx, hy, ← pow_add, show e + (K - e) = K by omega]
    · rw [g2, hy]; exact low_load hlow (by omega)
  -- the atoms but the stores, then the stores
  have hA : ∀ i ∈ ([] : List ℕ), IsCanonical128 (σ (.n i)) := by simp
  have hat : ∀ a ∈ atomsIn l5Pre, a.Holds rd σ := by
    refine atoms_holds_stores (S := l5S) (w := w) hidx hcanA hg hA
      (fun a ha hnS hns => Or.inl ?_) (fun _ a ha haS => ?_)
    · have := hneeds a ha
      simp only [hns, Bool.true_eq_false, false_or] at this
      rcases this with (((h | h) | h) | h) | h
      · exact absurd h hnS
      · subst h
        exact load_holds_of hnS (hg _ ha) (by rw [v16]; exact hbase)
      · subst h
        exact load_holds_of hnS (hg _ ha) (by have h := hda0; rw [← v43, ← v42] at h; exact h)
      · subst h
        exact load_holds_of hnS (hg _ ha) (by have h := hda1; rw [← v44, ← v42] at h; exact h)
      · cases a <;> simp only [isRcB, Bool.false_eq_true] at h
        rename_i x y t1 t2 k
        have hmemA : decide (Atom.rangeCheck x y t1 t2 k ∈ atomsIn l5Pre) = true := decide_eq_true ha
        have hrcs : (Atom.rangeCheck x y t1 t2 k) = .rangeCheck (.n 18) (.n 21) (.n 22) (.n 23) (.n 20) ∨
            (Atom.rangeCheck x y t1 t2 k) = .rangeCheck (.n 19) (.n 25) (.n 26) (.n 27) (.n 24) := by
          have hall : ((atomsIn l5Pre).filter isRcB) =
              [.rangeCheck (.n 18) (.n 21) (.n 22) (.n 23) (.n 20),
                .rangeCheck (.n 19) (.n 25) (.n 26) (.n 27) (.n 24)] := by decide +kernel
          have hm : Atom.rangeCheck x y t1 t2 k ∈ (atomsIn l5Pre).filter isRcB :=
            List.mem_filter.mpr ⟨ha, rfl⟩
          rw [hall] at hm
          simpa using hm
        rcases hrcs with e | e <;> rw [e] at hmemA ⊢
        · exact hrc (by omega) hex (by norm_num) hmemA v18
            (by rw [show σ (.n 20) = word 9272771591053052074 0 0 from
              gconst (k := 3) (by decide), word_gmax])
        · exact hrc (by omega) hes (by norm_num) hmemA v19
            (by rw [show σ (.n 24) = word 9272771591053052074 0 0 from
              gconst (k := 5) (by decide), word_gmax])
    · simp only [l5S, List.mem_cons, List.not_mem_nil, or_false] at haS
      rcases haS with rfl | rfl | rfl
      · show LoadHolds rd (σ (.n 48)) 0 (σ (.n 45))
        rw [v48', v47, e0, p12, v45]; exact hpi0
      · show LoadHolds rd (σ (.n 49)) 1 (σ (.n 46))
        rw [v49', v47, e0, p12, v46]; exact hpi1
      · show LoadHolds rd (σ (.n 57)) 1 (σ (.n 56))
        rw [v57', v56, p2, e0, v17, v28]; exact hnext
  refine ⟨hat, par, v16, v17, v18, v19, v28, v29, v30, v31, v32, v33, v34, ?_, v42, v43, v44,
    v45, v46, by rw [v48', v47, e0, p12]; rfl, by rw [v49', v47, e0, p12]; rfl, ?_,
    by rw [v57', e0, p2]; rfl, ?_, ?_⟩
  · rw [v40', h24, par 8 (by omega)]
  · rw [v55', h54, par 15 (by omega)]
  · rw [v60, v59, v58, e0, word_gen, gen_pow_mul_gen, par 1 (by omega)]
  · rw [v62', v61, e0, word_gen, gen_pow_mul_gen]

end
end LeanVM.Guest.B1.Main
