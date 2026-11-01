module

public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Bounds.FieldLib
public import LeanVM.Cost.Bounds.Decoder.PreTestDefs
public import LeanVM.Cost.Decoder.PreTest

/-!
# Bound: the decoder's precondition test, compiled

The prices of `Guest.Fast.preTestAt D T rd j fp` (`Cost/Decoder/PreTest.lean`), function `j`'s
precondition at the frame `fp` from the table `T` of the functions' preconditions, the
logarithm's baby-step tables `D` given. Parametric in what the test calls:

* a memory read: the reader closure `rdVal` at most `R` (the decoder's `memReaderC`,
  `Bounds/Decoder/DecoderEnds.lean`: `123 + 42κ`);
* a logarithm's bound: `powBelowC` at most `B`. `powBelow_cost` gives `B = Lg + 22` from the
  discrete logarithm's price `Lg` (`discreteLogWith D`, the compiled body the chain uses, and its
  logarithms word-sized); the logarithm is the one price that changes when the chain's
  logarithms do, so every other bound takes `B`;
* the exponents of an entry within `W` bits (`FnPreWithin`): a power `g^o` by squaring at most
  `psAt W = 6 + 535·W`.

The bounds, bottom-up: `powBelowAt_cost` (`6`), `readIs_cost` (`19`), `symVal_cost`, `envOne_cost`,
`readPowBelow_cost`, `bndOne_cost`, `memAt_cost`, `memCell_cost`, `memOne_cost`, `wordWith_cost`,
`powSqE_cost` (a power in `E` by squaring, `12 + 4732·(log₂ n + 1)`), `expOne_cost`,
`expTablesAt_cost` (the exponent tables' `34` entries: `68R + 5711272`), `semOne_cost`, then

* **`fnPreTest_cost`**: an entry's test at most `fnPrePrice W R B t` (`PreTestDefs.lean`);
* **`preTestAt_cost`**: function `j`'s test at most `fnPrePrice W R B (T.getD j none) + 18`;
* **`preTestAt_cost_deployed`**: on the deployed table (`preTable`, its shape evaluated in
  `PreTableShape.lean`: exponents below `2^7`, at most one check of each kind, at most `99`
  bounds and memory cells), at most `269R + 99B + 6528259`. With `B = Lg + 22` and the deployed
  reader (`R ≤ 123 + 42·32 = 1467`): `99·Lg + 6925060`, per call (≈ `2^22.7` beyond the
  logarithms). The semantic pair dominates: its `34` powers `gen^(2^j)` in `E` by squaring
  (`≤ 160900` each).
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Fast LeanVM.Extraction.Fast

public section

variable (P : LeanVM.Cost.MachineProgram)

/-! ## Powers and the logarithm's bound -/

/-- A power `g^o` by squaring, `o < 2^W`: at most `psAt W`. -/
theorem powSqW_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c198.costDeps) {W o : ℕ}
    (hW : 0 < W) (hW64 : W < 64) (ho : o < 2 ^ W) :
    machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c198.costIdx [encodeValue LeanVM.Parameters.g, encodeValue o] ≤
      psAt W := by
  have h64 : 2 ^ W ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hW64.le
  have h1 := powSq_cost P hP LeanVM.Parameters.g o (by omega)
  have h2 := log2_lt_of hW ho
  unfold psAt
  omega

/-- A power in `E` by squaring (`powSq.c534`): at most `12 + 4732·(log₂ n + 1)`. -/
theorem powSqE_cost (hP : Includes P Auto.LeanVM.Cost.Rewrite.powSq.c534.costDeps) (a : E) (n : ℕ)
    (hn : n < 2 ^ 64) :
    machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c534.costIdx [encodeValue a, encodeValue n] ≤
      12 + 4732 * (Nat.log2 n + 1) := by
  have := le_of_halving (fun x : E × ℕ ↦ x.2 < 2 ^ 64) (fun x ↦ x.2)
    (fun x ↦ machineCost P Auto.LeanVM.Cost.Rewrite.powSq.c534.costIdx
      [encodeValue x.1, encodeValue x.2]) 4732 12
    (fun x hx h0 ↦ by
      try dsimp only at hx h0 ⊢
      rw [Auto.LeanVM.Cost.Rewrite.powSq.c534.costEq P hP, h0]
      simp)
    (fun x hx hpos ↦ by
      try dsimp only at hx hpos ⊢
      right
      refine ⟨(x.1 * x.1, x.2 / 2), by dsimp only; omega, le_refl _, ?_⟩
      rw [Auto.LeanVM.Cost.Rewrite.powSq.c534.costEq P hP, limbs_of_lt hx,
        limbs_of_lt (by omega : x.2 % 2 < 2 ^ 64)]
      simp only [show x.2 ≠ 0 by omega, ↓reduceIte]
      split_ifs <;> omega)
    (a, n) hn
  simpa using this

/-- Whether a logarithm is below `n` (`powBelowAtC`): at most `6`, on word-sized numbers. -/
theorem powBelowAt_cost (hP : Includes P powBelowAtC.costDeps) (o : Option ℕ) (n : ℕ)
    (hn : n < 2 ^ 64) (ho : ∀ m, o = some m → m < 2 ^ 64) :
    machineCost P powBelowAtC.costIdx [encodeValue o, encodeValue n] ≤ 6 := by
  rw [powBelowAtC.costEq P hP]
  cases o with
  | none => dsimp only; omega
  | some m =>
    dsimp only
    rw [limbs_of_lt (ho m rfl), limbs_of_lt hn]
    simp only [max_self]
    omega

/-- **A logarithm's bound** (`powBelowC`): the discrete logarithm (at most `Lg`, its logarithms
word-sized) and `22`. -/
theorem powBelow_cost (hP : Includes P powBelowC.costDeps) (D : DiscreteLogTables) (Lg : ℕ)
    (hLg : ∀ x : K, machineCost P Auto.LeanVM.Extraction.Fast.discreteLogWith.c543.costIdx
      [encodeValue D, encodeValue x] ≤ Lg)
    (hD : ∀ x m, discreteLogWith D x = some m → m < 2 ^ 64) (w : E) (n : ℕ) (hn : n < 2 ^ 64) :
    machineCost P powBelowC.costIdx [encodeValue D, encodeValue w, encodeValue n] ≤ Lg + 22 := by
  rw [powBelowC.costEq P hP]
  have h1 := hLg (w.limb 0)
  have h2 := powBelowAt_cost P (by includes) _ n hn (hD (w.limb 0))
  split_ifs <;> omega

/-- Whether the word read is `x` (`readIsC`): at most `19`. -/
theorem readIs_cost (hP : Includes P readIsC.costDeps) (o : Option E) (x : E) :
    machineCost P readIsC.costIdx [encodeValue o, encodeValue x] ≤ 19 := by
  rw [readIsC.costEq P hP]
  cases o with
  | none => dsimp only; omega
  | some w => dsimp only; split_ifs <;> omega

/-- A known word's value (`symValC`): a power `g^e` and `269`. -/
theorem symVal_cost (hP : Includes P symValC.costDeps) {W : ℕ} (hW : 0 < W) (hW64 : W < 64)
    (fp : K) (a : Sym) (ha : symExp a < 2 ^ W) :
    machineCost P symValC.costIdx [encodeValue fp, encodeValue a] ≤ psAt W + 269 := by
  rw [symValC.costEq P hP]
  cases a with
  | zero => dsimp only; omega
  | gp e => have := powSqW_cost P (by includes) hW hW64 (o := e) ha; dsimp only; omega
  | fpg e => have := powSqW_cost P (by includes) hW hW64 (o := e) ha; dsimp only; omega

/-- The sum of an affine price over a list. -/
theorem sum_map_affine {α : Type} (f : α → ℕ) (a b : ℕ) :
    ∀ l : List α, (l.map fun x ↦ a * f x + b).sum = a * (l.map f).sum + b * l.length
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, sum_map_affine f a b l]
    ring

/-- `List.all` (`all.c240`), the predicate's price depending on the element: its prices and `9`
per element, `3`. -/
theorem all_cost_sum (hP : Includes P Auto.List.all.c240.costDeps) {β : Type} [MachineEncoding β]
    (p : β → Bool) (pVal : MachineValue)
    (hp : ∀ a, RunsApp P pVal [encodeValue a] (encodeValue (p a))) (B : β → ℕ) :
    ∀ l : List β, (∀ a ∈ l, appCost P pVal [encodeValue a] ≤ B a) →
      machineCost P Auto.List.all.c240.costIdx [encodeValue l, pVal] ≤
        (l.map fun a ↦ B a + 9).sum + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.all.c240.costEq_nil P hP p pVal hp]; simp
  | cons a l ih =>
    intro hB
    rw [Auto.List.all.c240.costEq_cons P hP a l p pVal hp]
    have h1 := ih fun a' ha ↦ hB a' (by simp [ha])
    have h2 := hB a (by simp)
    simp only [List.map_cons, List.sum_cons]
    split_ifs <;> omega

/-! ## The checks, one by one -/

section Checks

variable (D : DiscreteLogTables) (rd : Reader) (rdVal : MachineValue)
  (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
  (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)
  (B : ℕ) (hB : ∀ (w : E) (n : ℕ), n < 2 ^ 64 →
    machineCost P powBelowC.costIdx [encodeValue D, encodeValue w, encodeValue n] ≤ B)
  {W : ℕ} (hW : 0 < W) (hW64 : W < 64)

include hrd hW hW64

include hR in
/-- An entry-environment check (`envOneC`): two powers, a read and `557`. -/
theorem envOne_cost (hP : Includes P envOneC.costDeps) (fp : K) (p : ℕ × Sym)
    (h1 : p.1 < 2 ^ W) (h2 : symExp p.2 < 2 ^ W) :
    machineCost P envOneC.costIdx [rdVal, encodeValue fp, encodeValue p] ≤
      2 * psAt W + R + 557 := by
  rw [envOneC.costEq P hP rd rdVal hrd]
  have := powSqW_cost P (by includes) hW hW64 h1
  have := hR (fp * gpow p.1)
  have := symVal_cost P (by includes) hW hW64 fp p.2 h2
  have := readIs_cost P (by includes) (rd (fp * gpow p.1)) (p.2.val fp)
  omega

omit hrd hW hW64 in
include hB in
/-- A read's logarithm's bound (`readPowBelowC`): `B + 6`. -/
theorem readPowBelow_cost (hP : Includes P readPowBelowC.costDeps) (o : Option E) (n : ℕ)
    (hn : n < 2 ^ 64) :
    machineCost P readPowBelowC.costIdx [encodeValue D, encodeValue o, encodeValue n] ≤ B + 6 := by
  rw [readPowBelowC.costEq P hP]
  cases o with
  | none => dsimp only; omega
  | some w => have := hB w n hn; dsimp only; omega

include hR hB in
/-- A bound on a frame cell (`bndOneC`): a power, a read, a logarithm's bound and `274`. -/
theorem bndOne_cost (hP : Includes P bndOneC.costDeps) (fp : K) (p : ℕ × ℕ)
    (h1 : p.1 < 2 ^ W) (h2 : p.2 < 2 ^ 64) :
    machineCost P bndOneC.costIdx [encodeValue D, rdVal, encodeValue fp, encodeValue p] ≤
      psAt W + R + B + 274 := by
  rw [bndOneC.costEq P hP D rd rdVal hrd]
  have := powSqW_cost P (by includes) hW hW64 h1
  have := hR (fp * gpow p.1)
  have := readPowBelow_cost P D B hB (by includes) (rd (fp * gpow p.1)) p.2 h2
  omega

include hR hB in
/-- A memory bound at one cell (`memAtC`): a power, a read, a logarithm's bound and `283`. -/
theorem memAt_cost (hP : Includes P memAtC.costDeps) (n c : ℕ) (p : E) (hn : n < 2 ^ 64)
    (hc : c < 2 ^ W) :
    machineCost P memAtC.costIdx [encodeValue D, rdVal, encodeValue n, encodeValue c,
      encodeValue p] ≤ psAt W + R + B + 283 := by
  rw [memAtC.costEq P hP D rd rdVal hrd]
  have := powSqW_cost P (by includes) hW hW64 hc
  have := hR (p.limb 0 * gpow c)
  have := readPowBelow_cost P D B hB (by includes) (rd (p.limb 0 * gpow c)) n hn
  split_ifs <;> omega

include hR hB in
/-- A memory bound at one cell of the address in a frame cell (`memCellC`): two powers, two
reads, a logarithm's bound and `553`. -/
theorem memCell_cost (hP : Includes P memCellC.costDeps) (fp : K) (o n c : ℕ) (ho : o < 2 ^ W)
    (hn : n < 2 ^ 64) (hc : c < 2 ^ W) :
    machineCost P memCellC.costIdx [encodeValue D, rdVal, encodeValue fp, encodeValue o,
      encodeValue n, encodeValue c] ≤ 2 * psAt W + 2 * R + B + 553 := by
  rw [memCellC.costEq P hP D rd rdVal hrd]
  have := powSqW_cost P (by includes) hW hW64 ho
  have := hR (fp * gpow o)
  generalize rd (fp * gpow o) = r
  cases r with
  | none => dsimp only; omega
  | some p =>
    have := memAt_cost P D rd rdVal hrd R hR B hB hW hW64 (by includes) n c p hn hc
    dsimp only; omega

include hR hB in
/-- A memory bound (`memOneC`): per cell `2·psAt W + 2R + B + 586`, and `29`. -/
theorem memOne_cost (hP : Includes P memOneC.costDeps) (fp : K) (m : ℕ × ℕ × ℕ)
    (h1 : m.1 < 2 ^ W) (h2 : m.2.1 ≤ 2 ^ W) (h3 : m.2.2 < 2 ^ 64) :
    machineCost P memOneC.costIdx [encodeValue D, rdVal, encodeValue fp, encodeValue m] ≤
      (2 * psAt W + 2 * R + B + 586) * m.2.1 + 29 := by
  have h64 : 2 ^ W < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hW64
  rw [memOneC.costEq P hP D rd rdVal hrd]
  have hr := rangeLoop_cost P (by includes) m.2.1 [] (by omega)
  have ha := all_cost P (by includes) _
    (.closure memOneC.lam0.costIdx [encodeValue D, rdVal, encodeValue fp, encodeValue m.2.2,
      encodeValue m.1])
    (fun c ↦ RunsApp.of_spec (memOneC.lam0.costSpec P (by includes) D rd rdVal hrd fp m.2.2 m.1 c))
    (2 * psAt W + 2 * R + B + 560) (List.range m.2.1) (fun c hc ↦ by
      have hc' := List.mem_range.mp hc
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [memOneC.lam0.costEq P (by includes) D rd rdVal hrd]
      have := memCell_cost P D rd rdVal hrd R hR B hB hW hW64 (by includes) fp m.1 m.2.2 c h1 h3
        (by omega)
      omega)
  rw [List.length_range] at ha
  nlinarith

include hR in
/-- A frame cell's word (`wordWith.c709`): a power, a read and `271`. -/
theorem wordWith_cost (hP : Includes P Auto.LeanVM.Guest.Located.wordWith.c709.costDeps) (fp : K)
    (o : ℕ) (ho : o < 2 ^ W) :
    machineCost P Auto.LeanVM.Guest.Located.wordWith.c709.costIdx
      [rdVal, encodeValue fp, encodeValue o] ≤ psAt W + R + 271 := by
  rw [Auto.LeanVM.Guest.Located.wordWith.c709.costEq P hP rd rdVal hrd]
  have := powSqW_cost P (by includes) hW hW64 ho
  have := hR (fp * gpow o)
  generalize rd (fp * gpow o) = r
  cases r <;> dsimp only <;> omega

omit hW hW64 in
include hR in
/-- An entry of the exponent tables (`expOneC`), `j < 34`: two reads, two powers of `g`, a power
`gen^(2^j)` in `E` by squaring (at most `160900`): at most `2R + 167947`. -/
theorem expOne_cost (hP : Includes P expOneC.costDeps) (p q : E) (j : ℕ) (hj : j < 34) :
    machineCost P expOneC.costIdx [rdVal, encodeValue p, encodeValue q, encodeValue j] ≤
      2 * R + 167947 := by
  rw [expOneC.costEq P hP rd rdVal hrd, limbs_shift (by omega), limbs_of_lt (by omega : j < 2 ^ 64)]
  have hj' : j < 2 ^ 6 := by omega
  have h1 := powSqW_cost P (by includes) (W := 6) (by norm_num) (by norm_num) hj'
  have h2 := hR (p.limb 0 * gpow j)
  have h3 := hR (q.limb 0 * gpow j)
  have h4 := readIs_cost P (by includes) (rd (p.limb 0 * gpow j))
    (LeanVM.Protocol.Verifier.eOfNat (2 ^ j))
  have h5 := readIs_cost P (by includes) (rd (q.limb 0 * gpow j))
    (LeanVM.Protocol.Verifier.gen ^ 2 ^ j)
  have h6 := powSqE_cost P (by includes) LeanVM.Protocol.Verifier.gen (2 ^ j)
    (Nat.pow_lt_pow_right (by norm_num) (by omega))
  rw [Nat.log2_two_pow] at h6
  unfold psAt at h1
  split_ifs <;> omega

omit hW hW64 in
include hR in
/-- The exponent tables at two words (`expTablesAtC`): `34` entries, at most `68R + 5711272`. -/
theorem expTablesAt_cost (hP : Includes P expTablesAtC.costDeps) (p q : E) :
    machineCost P expTablesAtC.costIdx [rdVal, encodeValue p, encodeValue q] ≤
      68 * R + 5711272 := by
  rw [expTablesAtC.costEq P hP rd rdVal hrd]
  have hs : LeanVM.Guest.B1.sizeBits = 34 := rfl
  have hr := rangeLoop_cost P (by includes) LeanVM.Guest.B1.sizeBits [] (by rw [hs]; norm_num)
  have ha := all_cost P (by includes) _
    (.closure expTablesAtC.lam0.costIdx [rdVal, encodeValue p, encodeValue q])
    (fun j ↦ RunsApp.of_spec (expTablesAtC.lam0.costSpec P (by includes) rd rdVal hrd p q j))
    (2 * R + 167952) (List.range LeanVM.Guest.B1.sizeBits) (fun j hj ↦ by
      have hj' := List.mem_range.mp hj
      rw [hs] at hj'
      simp only [appCost_fn, List.cons_append, List.nil_append]
      rw [expTablesAtC.lam0.costEq P (by includes) rd rdVal hrd]
      have := expOne_cost P rd rdVal hrd R hR (by includes) p q j hj'
      omega)
  simp only [hs, List.length_range] at hr ha ⊢
  omega

include hR in
/-- A semantic pair (`semOneC`): two frame cells' words and the exponent tables at them: at most
`2·psAt W + 70R + 5711826`. -/
theorem semOne_cost (hP : Includes P semOneC.costDeps) (fp : K) (p : ℕ × ℕ) (h1 : p.1 < 2 ^ W)
    (h2 : p.2 < 2 ^ W) :
    machineCost P semOneC.costIdx [rdVal, encodeValue fp, encodeValue p] ≤
      2 * psAt W + 70 * R + 5711826 := by
  rw [semOneC.costEq P hP rd rdVal hrd]
  have := wordWith_cost P rd rdVal hrd R hR hW hW64 (by includes) fp p.1 h1
  have := wordWith_cost P rd rdVal hrd R hR hW hW64 (by includes) fp p.2 h2
  have := expTablesAt_cost P rd rdVal hrd R hR (by includes) (LeanVM.Guest.Located.wordWith rd fp p.1)
    (LeanVM.Guest.Located.wordWith rd fp p.2)
  omega

/-! ## An entry, and function `j` -/

include hR hB in
/-- **An entry's test** (`fnPreTestC`), its exponents within `W` bits: at most
`fnPrePrice W R B t`. -/
theorem fnPreTest_cost (hP : Includes P fnPreTestC.costDeps) (fp : K) (t : Option FnPre)
    (ht : ∀ s, t = some s → FnPreWithin W s) :
    machineCost P fnPreTestC.costIdx [encodeValue D, rdVal, encodeValue fp, encodeValue t] ≤
      fnPrePrice W R B t := by
  rw [fnPreTestC.costEq P hP D rd rdVal hrd]
  cases t with
  | none => dsimp only; simp [fnPrePrice]
  | some s =>
    obtain ⟨he, hpre, hm, hsem⟩ := ht s rfl
    dsimp only
    have h1 := all_cost P (by includes) _
      (.closure fnPreTestC.lam0.costIdx [rdVal, encodeValue fp])
      (fun p ↦ RunsApp.of_spec (fnPreTestC.lam0.costSpec P (by includes) rd rdVal hrd fp p))
      (2 * psAt W + R + 561) s.env (fun p hp ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [fnPreTestC.lam0.costEq P (by includes) rd rdVal hrd]
        have := envOne_cost P rd rdVal hrd R hR hW hW64 (by includes) fp p (he p hp).1 (he p hp).2
        omega)
    have h2 := all_cost P (by includes) _
      (.closure fnPreTestC.lam1.costIdx [encodeValue D, rdVal, encodeValue fp])
      (fun p ↦ RunsApp.of_spec (fnPreTestC.lam1.costSpec P (by includes) D rd rdVal hrd fp p))
      (psAt W + R + B + 279) s.pre (fun p hp ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [fnPreTestC.lam1.costEq P (by includes) D rd rdVal hrd]
        have := bndOne_cost P D rd rdVal hrd R hR B hB hW hW64 (by includes) fp p (hpre p hp).1
          (hpre p hp).2
        omega)
    have h3 := all_cost_sum P (by includes) _
      (.closure fnPreTestC.lam2.costIdx [encodeValue D, rdVal, encodeValue fp])
      (fun m ↦ RunsApp.of_spec (fnPreTestC.lam2.costSpec P (by includes) D rd rdVal hrd fp m))
      (fun m ↦ (2 * psAt W + 2 * R + B + 586) * m.2.1 + 34) s.mem (fun m hm' ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [fnPreTestC.lam2.costEq P (by includes) D rd rdVal hrd]
        have := memOne_cost P D rd rdVal hrd R hR B hB hW hW64 (by includes) fp m (hm m hm').1
          (hm m hm').2.1 (hm m hm').2.2
        omega)
    have h4 := all_cost P (by includes) _
      (.closure fnPreTestC.lam3.costIdx [rdVal, encodeValue fp])
      (fun p ↦ RunsApp.of_spec (fnPreTestC.lam3.costSpec P (by includes) rd rdVal hrd fp p))
      (2 * psAt W + 70 * R + 5711830) s.sem (fun p hp ↦ by
        simp only [appCost_fn, List.cons_append, List.nil_append]
        rw [fnPreTestC.lam3.costEq P (by includes) rd rdVal hrd]
        have := semOne_cost P rd rdVal hrd R hR hW hW64 (by includes) fp p (hsem p hp).1
          (hsem p hp).2
        omega)
    have hsum : (s.mem.map fun m ↦ (2 * psAt W + 2 * R + B + 586) * m.2.1 + 34 + 9).sum =
        (2 * psAt W + 2 * R + B + 586) * memCells s + 43 * s.mem.length := by
      have := sum_map_affine (fun m : ℕ × ℕ × ℕ ↦ m.2.1) (2 * psAt W + 2 * R + B + 586) 43 s.mem
      unfold memCells
      rw [← this]
    rw [hsum] at h3
    unfold fnPrePrice
    split_ifs <;> nlinarith

include hR hB in
/-- **Function `j`'s precondition test** (`preTestAtC`), its entry's exponents within `W` bits:
at most `fnPrePrice W R B (T.getD j none) + 18`. -/
theorem preTestAt_cost (hP : Includes P preTestAtC.costDeps) (T : Array (Option FnPre)) (j : ℕ)
    (hj : j < 2 ^ 64) (fp : K) (hT : ∀ s, T.getD j none = some s → FnPreWithin W s) :
    machineCost P preTestAtC.costIdx [encodeValue D, encodeValue T, rdVal, encodeValue j,
      encodeValue fp] ≤ fnPrePrice W R B (T.getD j none) + 18 := by
  rw [preTestAtC.costEq P hP D T rd rdVal hrd, limbs_of_lt hj,
    limbs_of_lt (by unfold LeanVM.Guest.nFns; norm_num : LeanVM.Guest.nFns < 2 ^ 64)]
  have := fnPreTest_cost P D rd rdVal hrd R hR B hB hW hW64 (by includes) fp (T.getD j none) hT
  simp only [max_self]
  split_ifs <;> omega

end Checks

/-! ## The deployed table -/

/-- An entry of the deployed shape has its exponents within `7` bits. -/
theorem fnPreWithin_of_shape {t : FnPre} (h : fnPreShape t = true) : FnPreWithin 7 t := by
  simp only [fnPreShape, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, he⟩, hp⟩, hm⟩, hs⟩ := h
  exact ⟨fun p hp' ↦ he p hp', fun p hp' ↦ hp p hp', fun m hm' ↦ ⟨(hm m hm').1.1, (hm m hm').1.2, (hm m hm').2⟩,
    fun p hp' ↦ hs p hp'⟩

/-- **An entry of the deployed shape**: its test's price at most `269R + 99B + 6528241`. -/
theorem fnPrePrice_of_shape {t : FnPre} (h : fnPreShape t = true) (R B : ℕ) :
    fnPrePrice 7 R B (some t) ≤ 269 * R + 99 * B + 6528241 := by
  simp only [fnPreShape, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨he, hp⟩, hm⟩, hs⟩, hpc⟩, -⟩, -⟩, -⟩, -⟩ := h
  simp only [fnPrePrice, psAt]
  generalize t.env.length = e at *
  generalize t.pre.length = p at *
  generalize t.mem.length = m at *
  generalize t.sem.length = s at *
  generalize memCells t = c at *
  have h1 : (2 * (6 + 535 * 7) + R + 570) * e ≤ (2 * (6 + 535 * 7) + R + 570) * 1 :=
    Nat.mul_le_mul_left _ he
  have h2 : (6 + 535 * 7 + R + B + 288) * p + (2 * (6 + 535 * 7) + 2 * R + B + 586) * c ≤
      (2 * (6 + 535 * 7) + 2 * R + B + 586) * (p + c) := by nlinarith
  have h3 : (2 * (6 + 535 * 7) + 2 * R + B + 586) * (p + c) ≤
      (2 * (6 + 535 * 7) + 2 * R + B + 586) * 99 := Nat.mul_le_mul_left _ hpc
  have h4 : (2 * (6 + 535 * 7) + 70 * R + 5711859) * s ≤ (2 * (6 + 535 * 7) + 70 * R + 5711859) * 1 :=
    Nat.mul_le_mul_left _ hs
  nlinarith

/-- An entry of a table of the deployed shape has that shape. -/
theorem fnPreShape_of_getD {T : Array (Option FnPre)} (hT : tableShape T = true) {j : ℕ}
    {s : FnPre} (hs : T.getD j none = some s) : fnPreShape s = true := by
  unfold tableShape at hT
  rw [List.all_eq_true] at hT
  by_cases hj : j < T.size
  · have hmem : T[j] ∈ T.toList := Array.getElem_mem_toList hj
    have h2 : Option.all fnPreShape (T.getInternal j hj) = true := hT _ hmem
    simp only [Array.getD, hj, ↓reduceDIte] at hs
    rw [hs] at h2
    simpa using h2
  · simp [Array.getD, hj] at hs

/-- **Function `j`'s precondition test on a table of the deployed shape** (`preTable`:
`preTable_shape`, `PreTableShape.lean`): at most `269R + 99B + 6528259`. -/
theorem preTestAt_cost_deployed (hP : Includes P preTestAtC.costDeps) (D : DiscreteLogTables)
    (rd : Reader) (rdVal : MachineValue)
    (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
    (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)
    (B : ℕ) (hB : ∀ (w : E) (n : ℕ), n < 2 ^ 64 →
      machineCost P powBelowC.costIdx [encodeValue D, encodeValue w, encodeValue n] ≤ B)
    (T : Array (Option FnPre)) (hT : tableShape T = true) (j : ℕ) (hj : j < 2 ^ 64) (fp : K) :
    machineCost P preTestAtC.costIdx [encodeValue D, encodeValue T, rdVal, encodeValue j,
      encodeValue fp] ≤ 269 * R + 99 * B + 6528259 := by
  have := preTestAt_cost P D rd rdVal hrd R hR B hB (W := 7) (by norm_num) (by norm_num) hP T j hj
    fp (fun s hs ↦ fnPreWithin_of_shape (fnPreShape_of_getD hT hs))
  cases hg : T.getD j none with
  | none => rw [hg] at this; simp only [fnPrePrice] at this; omega
  | some s =>
    rw [hg] at this
    have := fnPrePrice_of_shape (fnPreShape_of_getD hT hg) R B
    omega

end

end LeanVM.Cost.Bounds
