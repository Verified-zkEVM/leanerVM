/-
  LeanVM.Guest.B1.VerifySub.Tail

  `verify_sub`'s calls, the ring map's challenges, its tail, and the memory's size.
-/

module

public import LeanVM.Guest.B1.VerifySub.Front

/-!
# The calls and the tail of `verify_sub`

* `vsCallsT_holds`: the three calls (`verify_bus_gkr`, `verify_tables`, `verify_keccak`) on their
  argument words, the cursor `stream·g^10`, the keccak table's `g^τ` from `dims_g`, the output
  lanes at `claim_pool·g^110`, the capacity copied;
* `vsMapsT_holds`: the ring map's challenges, the first `verify_keccak`'s, five squeezed;
* `vsTailT_holds`: `certify_placement`, the stack's log, the two range checks, the dispatch, the
  terminal, the deferred claim's words, and the return;
* `mem_size`: a memory image holding `n` words at one pointer has at least `n` words.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

theorem word_1024 : word 1024 0 0 = gen ^ 10 := by
  rw [show (1024 : ℕ) = 2 ^ 10 from rfl]; exact word_two_pow (by decide)

/-- **The three calls** (G:3243-3255). -/
theorem vsCallsT_holds (h : Stmt.HoldsList C rd σ vsCallsT next kret) :
    σ (.n 838) = σ (.n 27) * gen ^ 10 ∧
    C "verify_bus_gkr" [σ (.n 825), σ (.n 826), σ (.n 827), σ (.n 828), σ (.n 829), σ (.n 838),
      σ (.n 522), σ (.n 523)] ((List.range 9).map fun k ↦ σ (.n (839 + k))) ∧
    C "verify_tables" [σ (.n 839), σ (.n 840), σ (.n 841), σ (.n 842), σ (.n 843), σ (.n 844),
      σ (.n 0), σ (.n 1), σ (.n 523), σ (.n 522), σ (.n 129), σ (.n 28), σ (.n 149), σ (.n 5),
      σ (.n 640), σ (.n 836), σ (.n 7), σ (.n 8), σ (.n 848), σ (.n 845), σ (.n 846), σ (.n 847)]
      ((List.range 9).map fun k ↦ σ (.n (849 + k))) ∧
    LoadHolds rd (σ (.n 129)) 6 (σ (.n 858)) ∧ σ (.n 862) = σ (.n 7) * word 1899956092796928 0 0 ∧
    C "verify_keccak" [σ (.n 849), σ (.n 850), σ (.n 851), σ (.n 852), σ (.n 853), σ (.n 854),
      σ (.n 858), σ (.n 848), σ (.n 862), σ (.n 859), σ (.n 860)]
      ((List.range 8).map fun k ↦ σ (.n (863 + k))) ∧
    (∀ i < 5, σ (.n (871 + i)) = σ (.n (863 + i))) ∧ next := by
  simp only [vsCallsT, vsConst, vsMul, vsCall, vsAlloc, vsLd, holdsList_append, Stmt.HoldsList,
    Stmt.Holds, List.map_cons, List.map_nil, List.map_map] at h
  obtain ⟨c837, m838, cg, -, ct, l858, -, -, c861, m862, ck, h⟩ := h
  simp only [Atom.Holds] at c837 m838 c861 m862
  refine ⟨by rw [m838, c837, word_1024], ?_, ?_, l858, by rw [m862, c861], ?_, ?_, ?_⟩
  · simpa [Function.comp_def] using cg
  · simpa [Function.comp_def] using ct
  · simpa [Function.comp_def] using ck
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
    intro i hi
    interval_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.1
  · simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
    exact h.2.2.2.2.2

/-- **The ring map's challenges** (G:3264-3270): the first `verify_keccak`'s, five squeezed from
the capacity it returned. -/
theorem vsMapsT_holds (h10 : σ (.n 10) = 0) (h11 : σ (.n 11) = 0) (h12 : σ (.n 12) = 0)
    (h13 : σ (.n 13) = 0) (h : Stmt.HoldsList C rd σ vsMapsT next kret) :
    (⟨[σ (.n 871), σ (.n 872), σ (.n 873), σ (.n 874), σ (.n 875)], []⟩ : Fs).squeezeN 5 =
      ([σ (.n 897), σ (.n 917), σ (.n 937), σ (.n 957), σ (.n 977)],
        ⟨[σ (.n 966), σ (.n 967), σ (.n 968), σ (.n 969), σ (.n 970)], []⟩) ∧
      ReadsAt rd (σ (.n 876))
        [σ (.n 870), σ (.n 897), σ (.n 917), σ (.n 937), σ (.n 957), σ (.n 977)] ∧ next := by
  simp only [vsMapsT, holdsList_append] at h
  obtain ⟨-, -, l0, h⟩ := h
  obtain ⟨s1, l1, h⟩ := vsSqzT_holds h10 h11 h12 h13 h
  obtain ⟨s2, l2, h⟩ := vsSqzT_holds h10 h11 h12 h13 h
  obtain ⟨s3, l3, h⟩ := vsSqzT_holds h10 h11 h12 h13 h
  obtain ⟨s4, l4, h⟩ := vsSqzT_holds h10 h11 h12 h13 h
  obtain ⟨s5, l5, hn⟩ := vsSqzT_holds h10 h11 h12 h13 h
  have e1 : (⟨[σ (.n 871), σ (.n 872), σ (.n 873), σ (.n 874), σ (.n 875)], []⟩ : Fs).squeeze =
      (σ (.n 897), ⟨[σ (.n 886), σ (.n 887), σ (.n 888), σ (.n 889), σ (.n 890)], []⟩) := s1
  have e2 : (⟨[σ (.n 886), σ (.n 887), σ (.n 888), σ (.n 889), σ (.n 890)], []⟩ : Fs).squeeze =
      (σ (.n 917), ⟨[σ (.n 906), σ (.n 907), σ (.n 908), σ (.n 909), σ (.n 910)], []⟩) := s2
  have e3 : (⟨[σ (.n 906), σ (.n 907), σ (.n 908), σ (.n 909), σ (.n 910)], []⟩ : Fs).squeeze =
      (σ (.n 937), ⟨[σ (.n 926), σ (.n 927), σ (.n 928), σ (.n 929), σ (.n 930)], []⟩) := s3
  have e4 : (⟨[σ (.n 926), σ (.n 927), σ (.n 928), σ (.n 929), σ (.n 930)], []⟩ : Fs).squeeze =
      (σ (.n 957), ⟨[σ (.n 946), σ (.n 947), σ (.n 948), σ (.n 949), σ (.n 950)], []⟩) := s4
  have e5 : (⟨[σ (.n 946), σ (.n 947), σ (.n 948), σ (.n 949), σ (.n 950)], []⟩ : Fs).squeeze =
      (σ (.n 977), ⟨[σ (.n 966), σ (.n 967), σ (.n 968), σ (.n 969), σ (.n 970)], []⟩) := s5
  refine ⟨by simp only [Fs.squeezeN, e1, e2, e3, e4, e5], fun k hk ↦ ?_, hn⟩
  simp only [List.length_cons, List.length_nil] at hk
  interval_cases k
  · exact l0
  · exact l1
  · exact l2
  · exact l3
  · exact l4
  · exact l5

/-- Copies of `n` words, `p[k]` to `q[qo k]`, through the values `b + k`. -/
theorem holds_copyLoads (p q b : ℕ) (qo : ℕ → ℕ) : ∀ (n : ℕ) {X : Prop},
    Stmt.HoldsList C rd σ ((List.range n).flatMap fun k ↦ [vsLd (b + k) p k, vsLd (b + k) q (qo k)])
      X kret → (∀ k < n, ∃ v, LoadHolds rd (σ (.n p)) k v ∧ LoadHolds rd (σ (.n q)) (qo k) v) ∧ X
  | 0, X, h => ⟨fun k hk ↦ absurd hk (Nat.not_lt_zero k), h⟩
  | n + 1, X, h => by
    rw [List.range_succ, List.flatMap_append, holdsList_append] at h
    obtain ⟨hk, h⟩ := holds_copyLoads p q b qo n h
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Stmt.HoldsList, Stmt.Holds,
      vsLd, Atom.Holds] at h
    obtain ⟨l1, l2, hX⟩ := h
    refine ⟨fun k hk' ↦ ?_, hX⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hk' | rfl
    · exact hk k hk'
    · exact ⟨_, l1, l2⟩

/-- **The tail** (G:3301-3336): the placement, the stack's log `g^m`, `size_sel = g^m·g^-22` below
`g^7`, the candidate `size_sel·rate_sel^7` below `g^28`, one specialization of `open_stacked`
dispatched on it, the terminal, the deferred claim's words, and no return word. -/
theorem vsTailT_holds (h : Stmt.HoldsList C rd σ vsTailT next kret) :
    C "certify_placement" [σ (.n 141), σ (.n 5)] [σ (.n 1887), σ (.n 1888), σ (.n 1889)] ∧
    C "log2_ceil_in_the_exponent__L15_L34" [σ (.n 1887), σ (.n 4), σ (.n 5)] [σ (.n 1890)] ∧
    σ (.n 1892) = σ (.n 1890) * word 8198552432976855044 0 0 ∧
    (LoadHolds rd (σ (.n 1892)) 0 (σ (.n 1895)) ∧ word 64 0 0 = σ (.n 1892) * σ (.n 1894) ∧
      LoadHolds rd (σ (.n 1894)) 0 (σ (.n 1896))) ∧
    σ (.n 1901) = σ (.n 1892) * (σ (.n 124) * σ (.n 124) * σ (.n 124) *
      (σ (.n 124) * σ (.n 124) * σ (.n 124)) * σ (.n 124)) ∧
    (LoadHolds rd (σ (.n 1901)) 0 (σ (.n 1904)) ∧ word 134217728 0 0 = σ (.n 1901) * σ (.n 1903) ∧
      LoadHolds rd (σ (.n 1903)) 0 (σ (.n 1905))) ∧
    (∃ (j : ℕ) (hj : j < vsOpenNames.length), σ (.n 1901) = ofK (gpow j) ∧
      C vsOpenNames[j] [σ (.n 1312), σ (.n 1313), σ (.n 1314), σ (.n 1315), σ (.n 1316),
        σ (.n 1886), σ (.n 537), σ (.n 547), σ (.n 868)]
        [σ (.n 1906), σ (.n 1907), σ (.n 1908), σ (.n 1909), σ (.n 1910)]) ∧
    C "check_opening_terminal" [σ (.n 523), σ (.n 848), σ (.n 857), σ (.n 522), σ (.n 855),
      σ (.n 130), σ (.n 858), σ (.n 8), σ (.n 1884), σ (.n 1324), σ (.n 1888), σ (.n 1889),
      σ (.n 859), σ (.n 877), σ (.n 1907), σ (.n 1908), σ (.n 1909), σ (.n 1910), σ (.n 1906)] [] ∧
    (∀ k < 19, ∃ v, LoadHolds rd (σ (.n 523)) k v ∧ LoadHolds rd (σ (.n 6)) k v) ∧
    (∀ k < 4, ∃ v, LoadHolds rd (σ (.n 559)) k v ∧ LoadHolds rd (σ (.n 6)) (19 + k) v) ∧
    LoadHolds rd (σ (.n 6)) 23 (σ (.n 856)) ∧ kret [] := by
  rw [vsTailT] at h
  simp only [holdsList_append] at h
  simp only [vsConst, vsMul, vsCall, vsRange, vsLd, vsRun, Stmt.HoldsList, Stmt.Holds,
    List.map_cons, List.map_nil] at h
  obtain ⟨cp, cl, c1891, m1892, c1893, r1, m1897, m1898, m1899, m1900, m1901, c1902, r2, hd, ct,
    h⟩ := h
  obtain ⟨d1, h⟩ := holds_copyLoads 523 6 1911 (fun k ↦ k) 19 h
  obtain ⟨d2, h⟩ := holds_copyLoads 559 6 1930 (fun k ↦ 19 + k) 4 h
  simp only [Atom.Holds] at c1891 m1892 c1893 r1 m1897 m1898 m1899 m1900 m1901 c1902 r2 h
  refine ⟨cp, cl, by rw [m1892, c1891], by rw [← c1893]; exact r1, ?_, by rw [← c1902]; exact r2,
    ?_, ct, d1, d2, h.1, by simpa using h.2⟩
  · rw [m1901, m1900, m1899, m1898, m1897]
  · obtain ⟨j, hj, hx, hc⟩ := hd
    exact ⟨j, hj, hx, by simpa [List.range_succ] using hc⟩

/-! ## The memory's size -/

/-- **A memory image holding `n` words at one pointer has at least `n` words.** -/
theorem mem_size {κ : ℕ} (hκ : κ ≤ 32) (L : MemImage κ) {p : E} {n : ℕ} (hn : n ≤ 2 ^ 32)
    (h : ∀ j < n, ∃ v, LoadHolds L.read p j v) : n ≤ 2 ^ κ := by
  have hκ64 : κ < 64 := by omega
  have hidx : ∀ j : Fin n, ∃ i : Fin (2 ^ κ), p.limb 0 * Parameters.gpow j = Parameters.gpow i := by
    intro j
    obtain ⟨v, -, hv⟩ := h j j.isLt
    obtain ⟨i, hi, -⟩ := (read_some_iff hκ64 L _ _).mp hv
    exact ⟨i, hi⟩
  choose f hf using hidx
  have hinj : Function.Injective f := by
    intro a b hab
    have ea := hf a
    have eb := hf b
    rw [hab, ← eb] at ea
    have hp : p.limb 0 ≠ 0 := by
      intro h0
      have := hf a
      rw [h0, zero_mul] at this
      exact Parameters.gpow_ne_zero _ this.symm
    have := mul_left_cancel₀ hp ea
    have hlt : ∀ x : Fin n, (x : ℕ) < 2 ^ 64 - 1 := fun x ↦ by have := x.isLt; omega
    exact Fin.ext (gpow_injOn (hlt a) (hlt b) this)
  simpa using Fintype.card_le_of_injective f hinj

end
end LeanVM.Guest.B1.VerifySub
