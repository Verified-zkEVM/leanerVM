/-
  LeanVM.Guest.B1.Main.KidBlockC

  `__loop5`'s block (a child) on its honest valuation: the block evaluated (`Fwd.ev`) on the
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

`l5W`: the oracle of the block's hints and calls' returns (the counts `g^ex`, `g^es`, `g^ed`, the
two claim lists' digests, the buffers `child_pi` at `g^P1` and the DA roots at `g^(P1 + 2)`, the DA
list's digest, the statement's digest). `l5_core`: on a memory defined below `2^16` holding
`written[x]`, the signer-set digest at `child_pi`, the statement's digest at `child_pi_table·x²` and
`written[x·g]`, every atom of the block holds on `l5σ`, with its words (`L5Vals`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Da (good_mul good_load)
open LeanVM.Guest.B1 (LowDef)

@[expose] public section

/-- The oracle of `__loop5`'s block. -/
def l5W (ex es ed P1 : ℕ) (cx0 cx1 cs0 cs1 d0 d1 p0 p1 : E) (j : ℕ) : E :=
  if j = 20 then gen ^ ex else if j = 21 then gen ^ es else if j = 32 then cx0
  else if j = 33 then cx1 else if j = 35 then cs0 else if j = 36 then cs1
  else if j = 56 then gen ^ P1 else if j = 63 then gen ^ ed else if j = 70 then gen ^ (P1 + 2)
  else if j = 74 then d0 else if j = 75 then d1 else if j = 76 then p0 else if j = 77 then p1
  else 0

/-- `__loop5`'s body. -/
def l5Body : List Stmt := l5Pre ++ [l5Tail, .ret []]

/-- `__loop5`'s honest valuation. -/
noncomputable def l5σ (rd : Reader) (args : List E) (w : ℕ → E) : Val :=
  B1.Val.ofArgs (ev rd w args l5Body)

/-- **The words of a child's block.** -/
structure L5Vals (rd : Reader) (σ : Val) (args : List E) (c ex es ed P1 : ℕ)
    (base cx0 cx1 cs0 cs1 d0 d1 p0 p1 : E) : Prop where
  atoms : ∀ a ∈ atomsIn l5Pre, a.Holds rd σ
  par : ∀ i < 18, σ (.n i) = args.getD i 0
  v18 : σ (.n 18) = args.getD 2 0 * gen ^ c
  v19 : σ (.n 19) = base
  v20 : σ (.n 20) = gen ^ ex
  v21 : σ (.n 21) = gen ^ es
  v30 : σ (.n 30) = gen ^ ex * gen ^ es
  v31 : σ (.n 31) = 1
  v32 : σ (.n 32) = cx0
  v33 : σ (.n 33) = cx1
  v34 : σ (.n 34) = base * gen ^ ex
  v35 : σ (.n 35) = cs0
  v36 : σ (.n 36) = cs1
  v56 : σ (.n 56) = gen ^ P1
  v62 : σ (.n 62) = args.getD 8 0 * gen ^ (24 * c)
  v63 : σ (.n 63) = gen ^ ed
  v69 : σ (.n 69) = gen ^ (4 * ed)
  v70 : σ (.n 70) = gen ^ (P1 + 2)
  v72 : σ (.n 72) = 1 + gen ^ ed
  v73 : σ (.n 73) = 1
  v74 : σ (.n 74) = d0
  v75 : σ (.n 75) = d1
  v76 : σ (.n 76) = p0
  v77 : σ (.n 77) = p1
  v79 : σ (.n 79) = args.getD 14 0 * (gen ^ c * gen ^ c)
  v80 : σ (.n 80) = args.getD 14 0 * (gen ^ c * gen ^ c)
  v86 : σ (.n 86) = args.getD 17 0 * gen ^ (24 * c)
  v89 : σ (.n 89) = args.getD 2 0 * gen ^ c
  v92 : σ (.n 92) = gen ^ (c + 1) + args.getD 1 0
  v94 : σ (.n 94) = gen ^ (c + 1)

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
set_option maxHeartbeats 8000000 in
/-- **A child's block holds** on its honest valuation. -/
theorem l5_core {rd : Reader} (hlow : LowDef 16 rd) {c : ℕ}
    {N written lxt cover lxs lst lss carried roots dcov dslots s0 s1 cpi glp gsq cfresh : E}
    {ex es ed P1 : ℕ} {base cx0 cx1 cs0 cs1 d0 d1 p0 p1 : E}
    (hex : ex ≤ 65535) (hes : es ≤ 65535) (hed : ed ≤ 16) (hcan : AllCanonical [cx0, cx1, cs0, cs1])
    (hbase : LoadHolds rd (written * gen ^ c) 0 base)
    (hsp0 : LoadHolds rd (gen ^ P1) 0 (digestScalars (keccak256 (cellsBytes [cx0, cx1, cs0, cs1]))).1)
    (hsp1 : LoadHolds rd (gen ^ P1) 1 (digestScalars (keccak256 (cellsBytes [cx0, cx1, cs0, cs1]))).2)
    (hpi0 : LoadHolds rd (cpi * (gen ^ c * gen ^ c)) 0 p0)
    (hpi1 : LoadHolds rd (cpi * (gen ^ c * gen ^ c)) 1 p1)
    (hnext : LoadHolds rd (written * gen ^ c) 1 (base * (gen ^ ex * gen ^ es) * gen ^ ed)) :
    L5Vals rd (l5σ rd [gen ^ c, N, written, lxt, cover, lxs, lst, lss, carried, roots, dcov, dslots,
        s0, s1, cpi, glp, gsq, cfresh] (l5W ex es ed P1 cx0 cx1 cs0 cs1 d0 d1 p0 p1))
      [gen ^ c, N, written, lxt, cover, lxs, lst, lss, carried, roots, dcov, dslots,
        s0, s1, cpi, glp, gsq, cfresh] c ex es ed P1 base cx0 cx1 cs0 cs1 d0 d1 p0 p1 := by
  have hok := l5c_ok
  unfold l5COk at hok
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hst⟩, hcanA⟩, hneeds⟩, hsp⟩, ho0⟩, ho1⟩, hcalls⟩ := hok
  set args : List E := [gen ^ c, N, written, lxt, cover, lxs, lst, lss, carried, roots, dcov,
    dslots, s0, s1, cpi, glp, gsq, cfresh] with hargs
  set w := l5W ex es ed P1 cx0 cx1 cs0 cs1 d0 d1 p0 p1 with hw
  set σ := l5σ rd args w with hσ
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd w l5Body args hchk
  rw [show args.length = 18 from rfl, show l5Body = l5Pre ++ [l5Tail, .ret []] from rfl, hst] at hgs
  have hg : ∀ a ∈ atomsIn l5Pre, Good rd l5S w σ a := fun a ha =>
    hgs (.atom a) (List.mem_append_left _ (Da.atom_mem_of_atomsIn ha))
  have par : ∀ i < 18, σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd w (l := args) hchk (by simpa [hargs] using hi)
  have hmem : ∀ a : Atom, decide (a ∈ atomsIn l5Pre) = true → Good rd l5S w σ a :=
    fun a ha => hg a (of_decide_eq_true ha)
  have gconst : ∀ {k : ℕ} (hk : k < l5Pre.length), GoodS rd l5S w σ l5Pre[k] :=
    fun hk => hgs _ (List.mem_append_left _ (List.getElem_mem hk))
  -- the words
  have e0 : σ (.n 0) = gen ^ c := par 0 (by omega)
  have p2 : σ (.n 2) = written := par 2 (by omega)
  have v18 : σ (.n 18) = written * gen ^ c := by
    rw [good_mul (by omega) (by omega) (hmem (.mul (.n 18) (.n 2) (.n 0)) (by decide +kernel)),
      p2, e0]
  have hS19 : Atom.load (.n 19) (.n 18) 0 ∉ l5S := by decide
  have v19 : σ (.n 19) = base := by
    rw [good_load hS19 (hmem _ (by decide +kernel)), v18, rdAt_of_load hbase]
  have hmeta := hmem (.hint (.witness "child_meta" (.stack [.n 20, .n 21]))) (by decide +kernel)
  have v20 : σ (.n 20) = gen ^ ex := hmeta (.n 20) (by simp)
  have v21 : σ (.n 21) = gen ^ es := hmeta (.n 21) (by simp)
  have v30 : σ (.n 30) = gen ^ ex * gen ^ es := by
    rw [good_mul (by omega) (by omega) (hmem (.mul (.n 30) (.n 20) (.n 21)) (by decide +kernel)),
      v20, v21]
  have v31 : σ (.n 31) = 1 := by
    rw [show σ (.n 31) = word 1 0 0 from gconst (k := 8) (by decide),
      word_one]
  have hcall : ∀ s ∈ l5Calls, GoodS rd l5S w σ s := by
    intro s hs
    obtain ⟨t, ht, he⟩ := List.any_eq_true.mp (hcalls s hs)
    rw [← stmtEqb_sound he]
    exact hgs t (List.mem_append_left _ ht)
  simp only [l5Calls, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    GoodS] at hcall
  obtain ⟨hcx, hcs, hdl, hsd⟩ := hcall
  have v32 : σ (.n 32) = cx0 := hcx.1
  have v33 : σ (.n 33) = cx1 := hcx.2
  have v35 : σ (.n 35) = cs0 := hcs.1
  have v36 : σ (.n 36) = cs1 := hcs.2
  have v74 : σ (.n 74) = d0 := hdl.1
  have v75 : σ (.n 75) = d1 := hdl.2
  have v76 : σ (.n 76) = p0 := hsd.1
  have v77 : σ (.n 77) = p1 := hsd.2
  have v34 : σ (.n 34) = base * gen ^ ex := by
    rw [good_mul (by omega) (by omega) (hmem (.mul (.n 34) (.n 19) (.n 20)) (by decide +kernel)),
      v19, v20]
  have v56 : σ (.n 56) = gen ^ P1 := hmem (.hint (.alloc (.n 56) 2)) (by decide +kernel)
  have v63 : σ (.n 63) = gen ^ ed :=
    hmem (.hint (.witness "child_da_count" (.stack [.n 63]))) (by decide +kernel) (.n 63) (by simp)
  have v70 : σ (.n 70) = gen ^ (P1 + 2) :=
    hmem (.hint (.allocDyn (.n 70) (.n 69))) (by decide +kernel)
  have mul' : ∀ {d x y : ℕ}, x < d → y < d → decide (Atom.mul (.n d) (.n x) (.n y) ∈ atomsIn l5Pre) = true →
      σ (.n d) = σ (.n x) * σ (.n y) := fun hx hy h => good_mul hx hy (hmem _ h)
  have v57 := mul' (d := 57) (x := 0) (y := 0) (by omega) (by omega) (by decide +kernel)
  have v58 := mul' (d := 58) (x := 57) (y := 0) (by omega) (by omega) (by decide +kernel)
  have v59 := mul' (d := 59) (x := 58) (y := 58) (by omega) (by omega) (by decide +kernel)
  have v60 := mul' (d := 60) (x := 59) (y := 59) (by omega) (by omega) (by decide +kernel)
  have v61 := mul' (d := 61) (x := 60) (y := 60) (by omega) (by omega) (by decide +kernel)
  have v62' := mul' (d := 62) (x := 8) (y := 61) (by omega) (by omega) (by decide +kernel)
  have v81 := mul' (d := 81) (x := 0) (y := 0) (by omega) (by omega) (by decide +kernel)
  have v82 := mul' (d := 82) (x := 81) (y := 0) (by omega) (by omega) (by decide +kernel)
  have v83 := mul' (d := 83) (x := 82) (y := 82) (by omega) (by omega) (by decide +kernel)
  have v84 := mul' (d := 84) (x := 83) (y := 83) (by omega) (by omega) (by decide +kernel)
  have v85 := mul' (d := 85) (x := 84) (y := 84) (by omega) (by omega) (by decide +kernel)
  have v86' := mul' (d := 86) (x := 17) (y := 85) (by omega) (by omega) (by decide +kernel)
  have v68 := mul' (d := 68) (x := 63) (y := 63) (by omega) (by omega) (by decide +kernel)
  have v69 := mul' (d := 69) (x := 68) (y := 68) (by omega) (by omega) (by decide +kernel)
  have v78 := mul' (d := 78) (x := 0) (y := 0) (by omega) (by omega) (by decide +kernel)
  have v79 := mul' (d := 79) (x := 14) (y := 78) (by omega) (by omega) (by decide +kernel)
  have v80 := mul' (d := 80) (x := 14) (y := 78) (by omega) (by omega) (by decide +kernel)
  have v87 := mul' (d := 87) (x := 19) (y := 30) (by omega) (by omega) (by decide +kernel)
  have v88 := mul' (d := 88) (x := 87) (y := 63) (by omega) (by omega) (by decide +kernel)
  have v89 := mul' (d := 89) (x := 2) (y := 0) (by omega) (by omega) (by decide +kernel)
  have v91 := mul' (d := 91) (x := 0) (y := 90) (by omega) (by omega) (by decide +kernel)
  have v94' := mul' (d := 94) (x := 0) (y := 93) (by omega) (by omega) (by decide +kernel)
  have v90 : σ (.n 90) = word 2 0 0 := gconst (k := 57) (by decide)
  have v93 : σ (.n 93) = word 2 0 0 := gconst (k := 60) (by decide)
  have v71 : σ (.n 71) = word 1 0 0 := gconst (k := 35) (by decide)
  have v73 : σ (.n 73) = word 1 0 0 := gconst (k := 37) (by decide)
  have v72 : σ (.n 72) = σ (.n 71) + σ (.n 63) := hmem (.add (.n 72) (.n 71) (.n 63)) (by decide +kernel)
  have v92 : σ (.n 92) = σ (.n 91) + σ (.n 1) := hmem (.add (.n 92) (.n 91) (.n 1)) (by decide +kernel)
  have h24 : σ (.n 61) = gen ^ (24 * c) := by
    rw [v61, v60, v59, v58, v57, e0, mul_comm 24 c, pow_mul]; ring
  have h85 : σ (.n 85) = gen ^ (24 * c) := by
    rw [v85, v84, v83, v82, v81, e0, mul_comm 24 c, pow_mul]; ring
  have p14 : σ (.n 14) = cpi := par 14 (by omega)
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
  have hA : ∀ i ∈ [32, 33, 35, 36], IsCanonical128 (σ (.n i)) := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · rw [v32]; exact hcan _ (by simp)
    · rw [v33]; exact hcan _ (by simp)
    · rw [v35]; exact hcan _ (by simp)
    · rw [v36]; exact hcan _ (by simp)
  have hat : ∀ a ∈ atomsIn l5Pre, a.Holds rd σ := by
    refine atoms_holds_stores (S := l5S) (w := w) hidx hcanA hg hA
      (fun a ha hnS hns => Or.inl ?_) (fun h1 a ha haS => ?_)
    · have := hneeds a ha
      simp only [hns, Bool.true_eq_false, false_or] at this
      rcases this with (h | h) | h
      · exact absurd h hnS
      · subst h
        exact load_holds_of hnS (hg _ ha) (by rw [v18]; exact hbase)
      · cases a <;> simp only [isRcB, Bool.false_eq_true] at h
        rename_i x y t1 t2 k
        have hmemA : decide (Atom.rangeCheck x y t1 t2 k ∈ atomsIn l5Pre) = true := decide_eq_true ha
        have hrcs : (Atom.rangeCheck x y t1 t2 k) = .rangeCheck (.n 20) (.n 23) (.n 24) (.n 25) (.n 22) ∨
            (Atom.rangeCheck x y t1 t2 k) = .rangeCheck (.n 21) (.n 27) (.n 28) (.n 29) (.n 26) ∨
            (Atom.rangeCheck x y t1 t2 k) = .rangeCheck (.n 63) (.n 65) (.n 66) (.n 67) (.n 64) := by
          have hall : ((atomsIn l5Pre).filter isRcB) =
              [.rangeCheck (.n 20) (.n 23) (.n 24) (.n 25) (.n 22),
                .rangeCheck (.n 21) (.n 27) (.n 28) (.n 29) (.n 26),
                .rangeCheck (.n 63) (.n 65) (.n 66) (.n 67) (.n 64)] := by decide +kernel
          have hm : Atom.rangeCheck x y t1 t2 k ∈ (atomsIn l5Pre).filter isRcB :=
            List.mem_filter.mpr ⟨ha, rfl⟩
          rw [hall] at hm
          simpa using hm
        rcases hrcs with e | e | e <;> rw [e] at hmemA ⊢
        · exact hrc (by omega) hex (by norm_num) hmemA v20
            (by rw [show σ (.n 22) = word 9272771591053052074 0 0 from
              gconst (k := 3) (by decide), word_gmax])
        · exact hrc (by omega) hes (by norm_num) hmemA v21
            (by rw [show σ (.n 26) = word 9272771591053052074 0 0 from
              gconst (k := 5) (by decide), word_gmax])
        · exact hrc (by omega) hed (by norm_num) hmemA v63
            (by rw [show σ (.n 64) = word 65536 0 0 from
              gconst (k := 30) (by decide), word_g16])
    · have hA' : ∀ b ∈ l5A', b.Holds rd σ :=
        fun b hb => h1 b (List.mem_filter.mp hb).1 (by simpa using (List.mem_filter.mp hb).2)
      obtain ⟨hd, -⟩ := chain_final hsp rfl hA' (pre := []) (n := 0) rfl
        (fun c => (cellsOfState_zero false c).symm)
      have hvals : ((pairSpec (.n 32) (.n 33) (.n 35) (.n 36) l5A').vals σ).take
          ((pairSpec (.n 32) (.n 33) (.n 35) (.n 36) l5A').len / 16) =
          [σ (.n 32), σ (.n 33), σ (.n 35), σ (.n 36)] := by
        simp [pairSpec, ChainSpec.vals, srcVal]
      rw [hvals, List.nil_append, ho0, ho1, v32, v33, v35, v36] at hd
      simp only [Prod.ext_iff] at hd
      simp only [l5S, List.mem_cons, List.not_mem_nil, or_false] at haS
      rcases haS with rfl | rfl | rfl | rfl | rfl
      · show LoadHolds rd (σ (.n 56)) 0 (σ (.n 43))
        rw [v56, hd.1]; exact hsp0
      · show LoadHolds rd (σ (.n 56)) 1 (σ (.n 44))
        rw [v56, hd.2]; exact hsp1
      · show LoadHolds rd (σ (.n 79)) 0 (σ (.n 76))
        rw [v79, v78, e0, p14, v76]; exact hpi0
      · show LoadHolds rd (σ (.n 80)) 1 (σ (.n 77))
        rw [v80, v78, e0, p14, v77]; exact hpi1
      · show LoadHolds rd (σ (.n 89)) 1 (σ (.n 88))
        rw [v89, v88, v87, p2, e0, v19, v30, v63]; exact hnext
  refine ⟨hat, par, v18, v19, v20, v21, v30, v31, v32, v33, v34, v35, v36, v56, ?_, v63, ?_, v70,
    ?_, by rw [v73, word_one], v74, v75, v76, v77, by rw [v79, v78, e0, par 14 (by omega)], by rw [v80, v78, e0, par 14 (by omega)], ?_,
    by rw [v89, e0, par 2 (by omega)], ?_, ?_⟩
  · rw [v62', h24, par 8 (by omega)]
  · rw [v69, v68, v63, mul_comm 4 ed, pow_mul]; ring
  · rw [v72, v71, word_one, v63]
  · rw [v86', h85, par 17 (by omega)]
  · rw [v92, v91, v90, e0, word_gen, gen_pow_mul_gen, par 1 (by omega)]
  · rw [v94', v93, e0, word_gen, gen_pow_mul_gen]

end
end LeanVM.Guest.B1.Main
