/-
  LeanVM.Guest.B1.VerifySub.C.Tail

  `verify_sub`'s tail (G:3294-3329), honestly: the placement, the stack's log and the candidate,
  the dispatch, the terminal, the deferred claim's cells.
-/

module

public import LeanVM.Guest.B1.VerifySub.C.Lam
public import LeanVM.Guest.B1.VerifySub.Known

/-!
# The tail, honestly

`vsTailPre_complete` (`vsTailPre`: the tail but its `ret`): with `certify_placement`'s and
`log2_ceil_in_the_exponent`'s calls in `C` returning the stack's log `g^m` (`22 ≤ m ≤ 28`), the
rate's power `g^(r - 1)` at `124` (`1 ≤ r ≤ 4`), the memory defined below `2^κ`, the candidate's
`open_stacked` call and the terminal's in `C`, and the deferred claim's cells in memory at `out`
(`6`: the bus point's `19` words, the four bus challenges, the bytecode value), the tail holds and
the candidate is `g^(candidate m r)`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Tables LeanVM.Protocol.Verifier

@[expose] public section

/-- The tail before its `ret`. -/
def vsTailPre : List Stmt := vsTailT.dropLast

theorem vsCPre_tail : vsCPre = vsHeadT ++ vsReadsT ++ vsSizesT ++ vsKappaT ++ vsPushT ++
    vsRootsT ++ vsAlphasT ++ vsFpwT ++ vsCallsT ++ vsMapsT ++ vsCtabT ++ vsLamT ++ vsTailPre :=
  stmtsEqb_sound (by decide +kernel)

/-- The tail's statements before its `ret`, explicitly. -/
def vsTailHead : List Stmt :=
  [vsCall "certify_placement" [141, 5] [1887, 1888, 1889],
    vsCall "log2_ceil_in_the_exponent__L15_L34" [1887, 4, 5] [1890],
    vsConst 1891 (word 8198552432976855044 0 0), vsMul 1892 1890 1891, vsConst 1893 (word 64 0 0),
    vsRange 1892 1894 1895 1896 1893, vsMul 1897 124 124, vsMul 1898 1897 124,
    vsMul 1899 1898 1898, vsMul 1900 1899 124, vsMul 1901 1892 1900,
    vsConst 1902 (word 134217728 0 0), vsRange 1901 1903 1904 1905 1902,
    .dispatch (.n 1901) vsOpenNames
      [.n 1312, .n 1313, .n 1314, .n 1315, .n 1316, .n 1886, .n 537, .n 547, .n 868] (vsRun 1906 5),
    vsCall "check_opening_terminal" [523, 848, 857, 522, 855, 130, 858, 8, 1884, 1324, 1888, 1889,
      859, 877, 1907, 1908, 1909, 1910, 1906] []]

theorem vsTailPre_eq : vsTailPre = vsTailHead ++
    (List.range 19).flatMap (fun k ↦ [vsLd (1911 + k) 523 k, vsLd (1911 + k) 6 k]) ++
    (List.range 4).flatMap (fun k ↦ [vsLd (1930 + k) 559 k, vsLd (1930 + k) 6 (19 + k)]) ++
    [vsLd 856 6 23] := stmtsEqb_sound (by decide +kernel)

theorem vsTailPre_noNe : vsTailPre.all noNeB = true := by decide +kernel

theorem vsTail_notS : (∀ k < 19, Atom.load (.n (1911 + k)) (.n 523) k ∉ vsSL) ∧
    ∀ k < 4, Atom.load (.n (1930 + k)) (.n 559) k ∉ vsSL := by decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

theorem vsTailPre_good (hl : args.length = 7) :
    ∀ s ∈ vsTailPre, GoodS rd vsSL w (vsσ rd w args) s := by
  intro s hs
  have h := vs_goodS (rd := rd) (w := w) hl (vs_mem_slice (n := 2084) (blk := vsTailPre)
    (by decide +kernel) hs)
  rwa [fixNe_of_noNe (List.all_eq_true.mp vsTailPre_noNe s hs)] at h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The tail, honestly.** -/
theorem vsTailPre_complete (hl : args.length = 7) {κ : ℕ} (hκ6 : 6 ≤ κ) (hlow : LowDef κ rd)
    {m r : ℕ} (hm22 : 22 ≤ m) (hm28 : m ≤ 28) (hr1 : 1 ≤ r) (hr4 : r ≤ 4)
    (e1890 : vsσ rd w args (.n 1890) = gen ^ m) (e124 : vsσ rd w args (.n 124) = gen ^ (r - 1))
    {zs al : ℕ → E}
    (hzeta : ∀ k < 19, LoadHolds rd (vsσ rd w args (.n 523)) k (zs k))
    (halpha : ∀ k < 4, LoadHolds rd (vsσ rd w args (.n 559)) k (al k))
    (hout : ∀ k < 19, LoadHolds rd (vsσ rd w args (.n 6)) k (zs k))
    (hout' : ∀ k < 4, LoadHolds rd (vsσ rd w args (.n 6)) (19 + k) (al k))
    (hout23 : LoadHolds rd (vsσ rd w args (.n 6)) 23 (vsσ rd w args (.n 856)))
    {C : CallRel}
    (hCcp : C "certify_placement" [vsσ rd w args (.n 141), vsσ rd w args (.n 5)]
      [vsσ rd w args (.n 1887), vsσ rd w args (.n 1888), vsσ rd w args (.n 1889)])
    (hClg : C "log2_ceil_in_the_exponent__L15_L34"
      [vsσ rd w args (.n 1887), vsσ rd w args (.n 4), vsσ rd w args (.n 5)]
      [vsσ rd w args (.n 1890)])
    (hD : C (vsOpenNames.getD (B1.Whir.candidate m r) "")
      ([1312, 1313, 1314, 1315, 1316, 1886, 537, 547, 868].map (vsσ rd w args ∘ V.n))
      ((vsRun 1906 5).map (vsσ rd w args)))
    (hCt : C "check_opening_terminal"
      ([523, 848, 857, 522, 855, 130, 858, 8, 1884, 1324, 1888, 1889, 859, 877, 1907, 1908, 1909,
        1910, 1906].map (vsσ rd w args ∘ V.n)) [])
    {next : Prop} {kret : List E → Prop} (hn : next) :
    vsσ rd w args (.n 1901) = gen ^ B1.Whir.candidate m r ∧
      Stmt.HoldsList C rd (vsσ rd w args) vsTailPre next kret := by
  have hG := vsTailPre_good (rd := rd) (w := w) hl
  generalize hσ : vsσ rd w args = σ at *
  have hκ : 64 ≤ 2 ^ κ :=
    calc 64 = 2 ^ 6 := rfl
      _ ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ6
  have mem : ∀ s ∈ vsTailHead, s ∈ vsTailPre := fun s hs ↦ by
    rw [vsTailPre_eq]; simp only [List.mem_append]; tauto
  have g : ∀ a, Stmt.atom a ∈ vsTailHead → Good rd vsSL w σ a := fun a h ↦ hG _ (mem _ h)
  have gm : ∀ (d x y : ℕ), vsMul d x y ∈ vsTailHead → x < d → y < d → σ (.n d) = σ (.n x) * σ (.n y) :=
    fun d x y h hx hy ↦ by
      have := g _ h
      simp only [Good] at this
      rwa [ite_eq_left_of_eq_true _ _ (eq_true ⟨show x < d from hx, show y < d from hy⟩)] at this
  have c1891 : σ (.n 1891) = word 8198552432976855044 0 0 :=
    g _ (show vsConst 1891 (word 8198552432976855044 0 0) ∈ vsTailHead by simp [vsTailHead])
  have c1893 : σ (.n 1893) = gen ^ 6 := by
    rw [show σ (.n 1893) = word 64 0 0 from g _ (show vsConst 1893 (word 64 0 0) ∈ vsTailHead by
      simp [vsTailHead]), show (64 : ℕ) = 2 ^ 6 from rfl, word_two_pow (by norm_num)]
  have c1902 : σ (.n 1902) = gen ^ 27 := by
    rw [show σ (.n 1902) = word 134217728 0 0 from g _ (show vsConst 1902 (word 134217728 0 0) ∈
      vsTailHead by simp [vsTailHead]), show (134217728 : ℕ) = 2 ^ 27 from rfl,
      word_two_pow (by norm_num)]
  have m1892 := gm 1892 1890 1891 (by simp [vsTailHead]) (by norm_num) (by norm_num)
  have v1892 : σ (.n 1892) = gen ^ (m - 22) := by
    rw [m1892, e1890, c1891]
    have : gen ^ m = gen ^ (m - 22) * gen ^ 22 := by rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc, mul_comm (gen ^ 22), kn_word_ginv22_mul, mul_one]
  have m1897 := gm 1897 124 124 (by simp [vsTailHead]) (by norm_num) (by norm_num)
  have m1898 := gm 1898 1897 124 (by simp [vsTailHead]) (by norm_num) (by norm_num)
  have m1899 := gm 1899 1898 1898 (by simp [vsTailHead]) (by norm_num) (by norm_num)
  have m1900 := gm 1900 1899 124 (by simp [vsTailHead]) (by norm_num) (by norm_num)
  have m1901 := gm 1901 1892 1900 (by simp [vsTailHead]) (by norm_num) (by norm_num)
  have v1900 : σ (.n 1900) = gen ^ (7 * (r - 1)) := by
    rw [m1900, m1899, m1898, m1897, e124, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1; ring
  have v1901 : σ (.n 1901) = gen ^ B1.Whir.candidate m r := by
    rw [m1901, v1892, v1900, ← pow_add]; rfl
  have hcand : B1.Whir.candidate m r ≤ 27 := by unfold B1.Whir.candidate; omega
  have r1 := rc_holds hlow (by decide) (a := m - 22) (b := 6 - (m - 22)) (by omega) (by omega)
    v1892 (by
      rw [good_rc_y (by decide) (g _ (show vsRange 1892 1894 1895 1896 1893 ∈ vsTailHead by
        simp [vsTailHead])), c1893, v1892, gen_pow_div (by omega)])
    (g _ (show vsRange 1892 1894 1895 1896 1893 ∈ vsTailHead by simp [vsTailHead]))
  have r2 := rc_holds hlow (by decide) (a := B1.Whir.candidate m r)
    (b := 27 - B1.Whir.candidate m r) (by omega) (by omega) v1901 (by
      rw [good_rc_y (by decide) (g _ (show vsRange 1901 1903 1904 1905 1902 ∈ vsTailHead by
        simp [vsTailHead])), c1902, v1901, gen_pow_div hcand])
    (g _ (show vsRange 1901 1903 1904 1905 1902 ∈ vsTailHead by simp [vsTailHead]))
  have hlen : vsOpenNames.length = 28 := by simp [vsOpenNames]
  have hdisp : ∃ (j : ℕ) (hj : j < vsOpenNames.length), σ (.n 1901) = ofK (gpow j) ∧
      C vsOpenNames[j] ([V.n 1312, V.n 1313, V.n 1314, V.n 1315, V.n 1316, V.n 1886, V.n 537,
        V.n 547, V.n 868].map σ) ((vsRun 1906 5).map σ) := by
    refine ⟨B1.Whir.candidate m r, by omega, by rw [v1901, gen_pow_eq_ofK], ?_⟩
    rw [← List.getD_eq_getElem _ ""]
    simpa using hD
  refine ⟨v1901, ?_⟩
  have k1893 : σ (.n 1893) = word 64 0 0 :=
    g _ (show vsConst 1893 (word 64 0 0) ∈ vsTailHead by simp [vsTailHead])
  have k1902 : σ (.n 1902) = word 134217728 0 0 :=
    g _ (show vsConst 1902 (word 134217728 0 0) ∈ vsTailHead by simp [vsTailHead])
  have memZ : ∀ k < 19, ∀ s ∈ [vsLd (1911 + k) 523 k, vsLd (1911 + k) 6 k], s ∈ vsTailPre :=
    fun k hk s hs ↦ by
      rw [vsTailPre_eq]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hs⟩)))
  have memA : ∀ k < 4, ∀ s ∈ [vsLd (1930 + k) 559 k, vsLd (1930 + k) 6 (19 + k)], s ∈ vsTailPre :=
    fun k hk s hs ↦ by
      rw [vsTailPre_eq]
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hs⟩))
  have L1 : ∀ l : List ℕ, (∀ k ∈ l, k < 19) → ∀ {nx : Prop}, nx →
      Stmt.HoldsList C rd σ (l.flatMap fun k ↦ [vsLd (1911 + k) 523 k, vsLd (1911 + k) 6 k])
        nx kret := by
    intro l
    induction l with
    | nil => intro _ nx h; exact h
    | cons k l ih =>
      intro hl' nx h
      have hk := hl' k List.mem_cons_self
      have r := good_read (w := w) (hG (vsLd (1911 + k) 523 k) (memZ k hk _ (by simp)))
        (vsTail_notS.1 k hk) (hzeta k hk)
      rw [List.flatMap_cons, holdsList_append]
      simp only [Stmt.HoldsList, Stmt.Holds, vsLd]
      refine ⟨r.2, by show LoadHolds rd _ _ _; rw [r.1]; exact hout k hk,
        ih (fun x hx ↦ hl' x (List.mem_cons_of_mem _ hx)) h⟩
  have L2 : ∀ l : List ℕ, (∀ k ∈ l, k < 4) → ∀ {nx : Prop}, nx →
      Stmt.HoldsList C rd σ (l.flatMap fun k ↦ [vsLd (1930 + k) 559 k, vsLd (1930 + k) 6 (19 + k)])
        nx kret := by
    intro l
    induction l with
    | nil => intro _ nx h; exact h
    | cons k l ih =>
      intro hl' nx h
      have hk := hl' k List.mem_cons_self
      have r := good_read (w := w) (hG (vsLd (1930 + k) 559 k) (memA k hk _ (by simp)))
        (vsTail_notS.2 k hk) (halpha k hk)
      rw [List.flatMap_cons, holdsList_append]
      simp only [Stmt.HoldsList, Stmt.Holds, vsLd]
      refine ⟨r.2, by show LoadHolds rd _ _ _; rw [r.1]; exact hout' k hk,
        ih (fun x hx ↦ hl' x (List.mem_cons_of_mem _ hx)) h⟩
  rw [vsTailPre_eq]
  simp only [holdsList_append]
  simp only [vsTailHead, Stmt.HoldsList, Stmt.Holds, vsCall, vsConst, vsMul, vsRange,
    List.map_cons, List.map_nil]
  simp only [List.map_cons, List.map_nil, Function.comp_apply] at hCt
  exact ⟨hCcp, hClg, c1891, m1892, k1893, r1, m1897, m1898, m1899, m1900, m1901, k1902, r2,
    hdisp, hCt, L1 _ (fun k hk ↦ List.mem_range.1 hk) (L2 _ (fun k hk ↦ List.mem_range.1 hk)
      ⟨hout23, hn⟩)⟩

end
end LeanVM.Guest.B1.VerifySub
