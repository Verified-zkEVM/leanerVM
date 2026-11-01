module

public import LeanVM.Guest.Fast.PreTable
public import LeanVM.Guest.Fast.DiscreteLog

/-!
# The precondition's test, from the table

`Located.preTestWith discreteLog rd j fp` decides function `j`'s precondition at the frame `fp`
(the replayed frame map's test, `Located/ReplayFast.lean`) from what a caller knows of `j`
(`glob.sig j`). `preTestAt D T Pw rd j fp` decides it from a table `T` of the functions'
preconditions (`FnPre`, `Fast/PreSig.lean`), the logarithm's baby-step tables `D`
(`discreteLogWith D`) and the powers `gen^(2^j)`, `j < 34`, of the exponent tables (`Pw`:
`genPows`, `34` squarings), all built once by the caller: one entry by its own function
(`fnPreTest`), each list of checks through a function of one check (`envOne`, `bndOne`, `memOne`,
`semOne`) by partial application, the logarithm passed as a value to `powBelowAt`, so that it
compiles to the cost machine (`Cost/Decoder/PreTest.lean`). (`discreteLog x` builds its tables at
every call, `7.8·10^7` on the cost machine.)

**`expTablesAt_genPows`**: with the powers table, the exponent tables' test is
`Located.expTablesTest` on every input (`semOne_genPows`).
**`preTestWith_eq_preTable`**: `preTestWith discreteLog = preTestAt discreteLogTables preTable
genPows`, the table the kernel wrote out (`Fast/PreTable.lean`); with `preTest_eq_discreteLog`,
`preTest_eq_preTable`.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.Exec LeanVM.Guest.Check
open LeanVM.Guest.Located LeanVM.Extraction.Fast

@[expose] public section

/-! ## The checks, one by one -/

/-- Whether the logarithm `o` of a word is below `n`. -/
def powBelowAt (o : Option ℕ) (n : ℕ) : Bool :=
  match o with
  | some m => decide (m < n)
  | none => false

/-- `w` is `g^e` for some `e < n` (`isPowBelow discreteLog`), the logarithm's baby-step tables
`D` given (`discreteLogWith`): its logarithm computed here and passed to `powBelowAt`. -/
def powBelow (D : DiscreteLogTables) (w : E) (n : ℕ) : Bool :=
  decide (IsInK w) && powBelowAt (discreteLogWith D (w.limb 0)) n

/-- The word read, if any, is `g^e` for some `e < n`. -/
def readPowBelow (D : DiscreteLogTables) (o : Option E) (n : ℕ) : Bool :=
  match o with
  | some w => powBelow D w n
  | none => false

/-- The word read, if any, is `x` (`decide (o = some x)`). -/
def readIs (o : Option E) (x : E) : Bool :=
  match o with
  | some w => decide (w = x)
  | none => false

/-- The entry environment's check `(o, v)`: cell `o` of the frame holds `v`. -/
def envOne (rd : Reader) (fp : K) (p : ℕ × Sym) : Bool :=
  readIs (rd (fp * gpow p.1)) (p.2.val fp)

/-- The bound `(o, n)`: cell `o` of the frame holds `g^e`, `e < n`. -/
def bndOne (D : DiscreteLogTables) (rd : Reader) (fp : K) (p : ℕ × ℕ) : Bool :=
  readPowBelow D (rd (fp * gpow p.1)) p.2

/-- The memory bound at the address `p`'s cell `c`: it holds `g^e`, `e < n`. -/
def memAt (D : DiscreteLogTables) (rd : Reader) (n c : ℕ) (p : E) : Bool :=
  decide (IsInK p) && readPowBelow D (rd (p.limb 0 * gpow c)) n

/-- The memory bound at cell `c` of the address in the frame's cell `o`. -/
def memCell (D : DiscreteLogTables) (rd : Reader) (fp : K) (o n c : ℕ) : Bool :=
  match rd (fp * gpow o) with
  | some p => memAt D rd n c p
  | none => false

/-- The memory bound `(o, len, n)`: for every `c < len`. -/
def memOne (D : DiscreteLogTables) (rd : Reader) (fp : K) (m : ℕ × ℕ × ℕ) : Bool :=
  (List.range m.2.1).all (memCell D rd fp m.1 m.2.2)

/-! ## The powers `gen^(2^j)`, a table built once -/

/-- `x, x^2, x^4, …`: `n` squarings. -/
def squaresFrom (x : E) : ℕ → List E
  | 0 => []
  | n + 1 => x :: squaresFrom (x * x) n

/-- **The powers `gen^(2^j)`, `j < 34`**, by `34` squarings: the exponent tables' right column,
built once by the caller and passed down (`Pw`). -/
def genPows : Array E := (squaresFrom Protocol.Verifier.gen B1.sizeBits).toArray

/-- Entry `j` of the exponent tables at `p`, `q` (`expTablesTest`), the powers `gen^(2^j)` read
off the table `Pw` (`genPows`). -/
def expOne (Pw : Array E) (rd : Reader) (p q : E) (j : ℕ) : Bool :=
  decide (IsInK p) && readIs (rd (p.limb 0 * gpow j)) (Protocol.Verifier.eOfNat (2 ^ j)) &&
    decide (IsInK q) && readIs (rd (q.limb 0 * gpow j)) (Pw.getD j 0)

/-- The exponent tables at `p`, `q`. -/
def expTablesAt (Pw : Array E) (rd : Reader) (p q : E) : Bool :=
  (List.range B1.sizeBits).all (expOne Pw rd p q)

/-- The semantic pair `(o₁, o₂)`: the exponent tables at the two cells' words. -/
def semOne (Pw : Array E) (rd : Reader) (fp : K) (p : ℕ × ℕ) : Bool :=
  expTablesAt Pw rd (wordWith rd fp p.1) (wordWith rd fp p.2)

/-- **A function's precondition at the frame `fp`**, from its entry of the table. -/
def fnPreTest (D : DiscreteLogTables) (Pw : Array E) (rd : Reader) (fp : K) (t : Option FnPre) :
    Bool :=
  match t with
  | none => true
  | some t => t.env.all (envOne rd fp) && t.pre.all (bndOne D rd fp) &&
      t.mem.all (memOne D rd fp) && t.sem.all (semOne Pw rd fp)

/-- **Function `j`'s precondition at the frame `fp`**, from the table `T` of the functions'
preconditions, the logarithm's baby-step tables `D` and the powers `Pw` (`genPows`) given (but
for the jump table, `preTest`). -/
def preTestAt (D : DiscreteLogTables) (T : Array (Option FnPre)) (Pw : Array E) (rd : Reader)
    (j : ℕ) (fp : K) : Bool :=
  decide (2 ≤ j) && decide (j < nFns) && fnPreTest D Pw rd fp (T.getD j none)

/-! ## They are the precondition's test -/

theorem readIs_eq (o : Option E) (x : E) : readIs o x = decide (o = some x) := by
  cases o <;> simp [readIs]

theorem envOne_eq (rd : Reader) (fp : K) (p : ℕ × Sym) :
    envOne rd fp p = decide (rd (fp * gpow p.1) = some (p.2.val fp)) :=
  readIs_eq _ _

theorem envTest_eq (rd : Reader) (fp : K) (env : List (ℕ × Sym)) :
    envTest rd fp env = (envChecks env).all (envOne rd fp) := by
  unfold envTest envChecks
  rw [List.all_filterMap]
  congr 1
  funext p
  cases (envOf env).get p.1 <;> simp [envOne_eq]

theorem powBelow_eq : isPowBelow discreteLog = powBelow discreteLogTables := by
  funext w n
  unfold isPowBelow powBelow powBelowAt
  rfl

theorem bndTestWith_eq_all (rd : Reader) (fp : K) (bnd : List (ℕ × ℕ)) :
    bndTestWith discreteLog rd fp bnd = bnd.all (bndOne discreteLogTables rd fp) := by
  unfold bndTestWith bndOne readPowBelow
  rw [powBelow_eq]
  rfl

theorem memTestWith_eq_all (rd : Reader) (fp : K) (mem : List (ℕ × ℕ × ℕ)) :
    memTestWith discreteLog rd fp mem = mem.all (memOne discreteLogTables rd fp) := by
  unfold memTestWith memOne memCell memAt readPowBelow
  rw [powBelow_eq]
  rfl

/-- The squarings are the powers `x^(2^j)`. -/
theorem squaresFrom_getD : ∀ (n : ℕ) (x : E) (j : ℕ), j < n → (squaresFrom x n).getD j 0 = x ^ 2 ^ j
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, 0, _ => by simp [squaresFrom]
  | n + 1, x, j + 1, h => by
    rw [squaresFrom, List.getD_cons_succ, squaresFrom_getD n (x * x) j (by omega), ← sq, ← pow_mul,
      pow_succ, mul_comm 2]

/-- **Entry `j < 34` of the powers table is `gen^(2^j)`.** -/
theorem genPows_getD {j : ℕ} (hj : j < B1.sizeBits) :
    genPows.getD j 0 = Protocol.Verifier.gen ^ 2 ^ j := by
  rw [genPows, Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
    squaresFrom_getD _ _ _ hj]

/-- **With the powers table, the exponent tables' test is `expTablesTest`**, on every input. -/
theorem expTablesAt_genPows (rd : Reader) (p q : E) :
    expTablesAt genPows rd p q = expTablesTest rd p q := by
  unfold expTablesAt expTablesTest
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_range]
  refine forall_congr' fun j ↦ forall_congr' fun hj ↦ ?_
  rw [expOne, genPows_getD hj]
  simp only [readIs_eq]

/-- **With the powers table, the semantic pair's test is the exponent tables at its cells'
words**, on every input. -/
theorem semOne_genPows (rd : Reader) (fp : K) (p : ℕ × ℕ) :
    semOne genPows rd fp p = expTablesTest rd (wordWith rd fp p.1) (wordWith rd fp p.2) :=
  expTablesAt_genPows rd _ _

theorem semTest_eq_all (rd : Reader) (fp : K) (sems : List (ℕ × ℕ)) :
    semTest rd fp sems = sems.all (semOne genPows rd fp) := by
  unfold semTest
  congr 1
  funext p
  rw [semOne_genPows]

/-- **The test of an entry `fnPreOf s` is the four tests of `s`.** -/
theorem fnPreTest_fnPreOf (rd : Reader) (fp : K) (s : Sig) :
    fnPreTest discreteLogTables genPows rd fp (fnPreOf s) =
      (envTest rd fp s.env && bndTestWith discreteLog rd fp s.pre &&
        memTestWith discreteLog rd fp s.mem && semTest rd fp s.sem) := by
  rw [envTest_eq, bndTestWith_eq_all, memTestWith_eq_all, semTest_eq_all]
  unfold fnPreOf
  cases h : (envChecks s.env).isEmpty && s.pre.isEmpty && s.mem.isEmpty && s.sem.isEmpty
  · rfl
  · simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    simp [fnPreTest, h1, h2, h3, h4]

/-- **From the table, the test is `preTestWith discreteLog`.** -/
theorem preTestWith_eq_preTable :
    preTestWith discreteLog = preTestAt discreteLogTables preTable genPows := by
  funext rd j fp
  unfold preTestWith preTestAt
  have hg : glob.good j = (decide (2 ≤ j) && decide (j < nFns)) := by
    show (Nat.ble 2 j && Nat.blt j nFns) = _
    exact Bool.eq_iff_iff.mpr (by simp [Nat.ble_eq, Nat.blt_eq])
  rw [hg]
  by_cases hj : 2 ≤ j ∧ j < nFns
  · rw [preTable_getD hj.2, fnPreTest_fnPreOf]
    simp [hj.1, hj.2, Bool.and_assoc]
  · rcases not_and_or.mp hj with h | h <;> simp [h]

/-- **The precondition's test is `preTestAt discreteLogTables preTable genPows`.** -/
theorem preTest_eq_preTable : preTest = preTestAt discreteLogTables preTable genPows :=
  preTest_eq_discreteLog.trans preTestWith_eq_preTable

end

end LeanVM.Guest.Fast
