/-
  LeanerVM.Arithmetization.WitnessGen

  The computable witness generator for a valid, fitting execution, and its correctness: the
  witness it returns satisfies the constraint statement and represents the padded trace.
-/

module

public import LeanerVM.Arithmetization.Completeness.Theorem
public import LeanerVM.Semantics.Generator

@[expose] public section

/-!
# The witness generator

`witnessGen prog input t` computes the witness `constraintCompleteness` proves exists:

* the fill starts are searched in the bytecode (`fillStartTable`, read by `startsOf`), the image
  padded with their frames (`padImage`), and the `JUMP` exponent searched (`jumpHeight`);
* the run is stepped forward once (`runSkelsBy`) at the checked-guess reader (`readBy`,
  `fetchBy`, with one table of powers `powTable`, which also writes the counts' powers and the
  memory block's addresses), its skeletons counted per table
  (`skelCountTable`), and the fill's skeletons appended (`padSkels`, `planCount`);
* the rows are written at the checked-guess reader (`rowOfBy`, a copy of `rowOf` reading through
  `limbsBy`/`cellBy`), with the read counters in hash maps (`mkRowsH`), and the tables are those of
  `padWitness` with the same rows (`padWitnessBy`).

**What is trusted here is the statement of `witnessGen_correct`**: on well-formed bytecode, every
valid execution that fits gets `some w`, with `w` satisfying `SatisfiedBy` and representing
`padTrace t (fillStarts prog)`. The proof reduces it to `padWitness_complete`: each computed
piece is proved equal to the reference one (`padWitnessBy_eq`, `runSkelsBy_eq_runSkels`), and the
searched choices are used through their specifications only.
`witnessGen_heights` gives the generated tables' heights in closed form: `tableHeight` of the
run's rows at the searched `JUMP` exponent.

## Wrong readings excluded

* The generator does not check the execution: on an invalid trace it may return a witness that
  satisfies nothing, and the theorem says nothing about it.
* The represented trace is the padded one, with the searched fill starts, not `t`
  (`Completeness.Theorem`).
-/

namespace LeanerVM.Arithmetization

open LeanerVM.Parameters LeanerVM.Semantics
open Air.Flat (EnsembleWitness)

/-! ## Rows at a reader -/

/-- `xorRowOf` at a reader. -/
def xorRowBy (rd : K → Option E) (pc fp oA oB oC rA rB rC rbc : K) : XorRow K :=
  ⟨pc, fp, oA, oB, oC, limbsBy rd (fp * oA), limbsBy rd (fp * oB), rA, rB, rC, rbc⟩

/-- `mulRowOf` at a reader. -/
def mulRowBy (rd : K → Option E) (pc fp oA oB oC rA rB rC rbc : K) : MulRow K :=
  ⟨pc, fp, oA, oB, oC, limbsBy rd (fp * oA), limbsBy rd (fp * oB), rA, rB, rC, rbc⟩

/-- `derefRowOf` at a reader. -/
def derefRowBy (rd : K → Option E) (pc fp o1 o2 o3 : K) (mode : DerefMode)
    (r1 r2 r3 rbc : K) : DerefRow K :=
  ⟨pc, fp, o1, o2, o3, (derefFlags mode).1, (derefFlags mode).2,
    (limbsBy rd (fp * o1))[0], limbsBy rd (fp * o3), r1, r2, r3, rbc⟩

/-- `jumpRowOf` at a reader. -/
def jumpRowBy (rd : K → Option E) (pc fp oc od of rc rdd rf rbc : K) : JumpRow K :=
  ⟨pc, fp, oc, od, of, (limbsBy rd (fp * oc))[0], (limbsBy rd (fp * od))[0],
    (limbsBy rd (fp * of))[0], rc, rdd, rf, rbc⟩

/-- `blake2sRowOf` at a reader. -/
def blake2sRowBy (rd : K → Option E) (pc fp om0 om1 om2 om3 ocv oout omd : K)
    (rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc : K) : Blake2sRow K :=
  ⟨pc, fp, om0, om1, om2, om3, ocv, oout, omd,
    cellBy rd (fp * om0), cellBy rd (fp * om1), cellBy rd (fp * om2), cellBy rd (fp * om3),
    cellBy rd (fp * oout), cellBy rd (fp * (g * oout)),
    cellBy rd (fp * ocv), cellBy rd (fp * (g * ocv)),
    cellBy rd (fp * omd),
    rm0, rm1, rm2, rm3, rcv0, rcv1, rout0, rout1, rmd, rbc⟩

/-- `rowOf` at a reader. -/
def rowOfBy (rd : K → Option E) (pc fp : K) (cnt : ℕ → K) (rbc : K) : Instr → Array K
  | .xor oA oB oC => rawRow (xorRowBy rd pc fp oA oB oC (cnt 0) (cnt 1) (cnt 2) rbc)
  | .mulNative oA oB oC => rawRow (mulRowBy rd pc fp oA oB oC (cnt 0) (cnt 1) (cnt 2) rbc)
  | .setConstant o k => rawRow (setRowOf pc fp o k (cnt 0) rbc)
  | .deref o1 o2 o3 mode =>
      rawRow (derefRowBy rd pc fp o1 o2 o3 mode (cnt 0) (cnt 1) (cnt 2) rbc)
  | .jump oc od of =>
      jumpRaw (jumpRowBy rd pc fp oc od of (cnt 0) (cnt 1) (cnt 2) rbc)
        (if (limbsBy rd (fp * oc))[0] = 0 then 0 else ((limbsBy rd (fp * oc))[0])⁻¹)
        (if (limbsBy rd (fp * oc))[0] = 0 then 0 else 1)
  | .blake2s om ocv oout omd =>
      rawRow (blake2sRowBy rd pc fp (om 0) (om 1) (om 2) (om 3) ocv oout omd
        (cnt 0) (cnt 1) (cnt 2) (cnt 3) (cnt 4) (cnt 5) (cnt 6) (cnt 7) (cnt 8) rbc)

/-- At the image's reader, the rows are `rowOf`'s. -/
theorem rowOfBy_read {κ : ℕ} (mem : MemImage κ) : rowOfBy mem.read = rowOf mem := by
  funext pc fp cnt rbc ins
  cases ins <;> rfl

/-- At the image's reader, the cells read are `readAddrs`'. -/
theorem readAddrsBy_read {κ : ℕ} (mem : MemImage κ) : readAddrsBy mem.read = readAddrs mem := by
  funext fp ins
  cases ins <;> rfl

/-! ## Read counters in hash maps -/

/-- Read counters keyed by the machine word of the address. -/
abbrev Counts : Type := Std.HashMap UInt64 ℕ

/-- The count of an address, `0` when unread. -/
def Counts.get (m : Counts) (a : K) : ℕ := m.getD (wordKey a) 0

/-- One more read of an address. -/
def Counts.bump (m : Counts) (a : K) : Counts := m.insert (wordKey a) (m.get a + 1)

/-- The numbers of a sequence of reads and the counters after it: `readExps` and `readBump`.
The count is read before the map is bumped, so that the map is updated in place. -/
def readExpsH : Counts → List K → List ℕ × Counts
  | m, [] => ([], m)
  | m, a :: rest =>
    let c := m.get a
    let p := readExpsH (m.insert (wordKey a) (c + 1)) rest
    (c :: p.1, p.2)

/-- The rows of a list of skeletons with their counters: `mkRows` at a reader, appended to `acc`,
and the counters after it. -/
def mkRowsH (rd : K → Option E) : Counts → Counts → List Skel → Array PRow →
    Array PRow × Counts × Counts
  | sm, sb, [], acc => (acc, sm, sb)
  | sm, sb, sk :: rest, acc =>
    let p := readExpsH sm (readAddrsBy rd sk.fp sk.ins)
    let c := sb.get sk.pc
    mkRowsH rd p.2 (sb.insert (wordKey sk.pc) (c + 1)) rest (acc.push ⟨sk, p.1, c⟩)

/-- Machine words determine field elements. -/
theorem wordKey_inj {a b : K} : wordKey a = wordKey b ↔ a = b := by
  refine ⟨fun h ↦ BF64.toBitVec_injective (congrArg UInt64.toBitVec h), fun h ↦ h ▸ rfl⟩

/-- No address of the empty counters has been read. -/
theorem Counts.get_empty : (∅ : Counts).get = fun _ ↦ 0 := by
  funext a
  exact Std.HashMap.getD_empty

/-- Bumping an address updates its count. -/
theorem Counts.get_bump (m : Counts) (a : K) :
    (m.bump a).get = Function.update m.get a (m.get a + 1) := by
  funext b
  rw [Counts.get, Counts.bump, Std.HashMap.getD_insert]
  by_cases h : a = b
  · subst h
    simp [Counts.get]
  · have h' : (wordKey a == wordKey b) = false := by
      simpa using fun e ↦ h (wordKey_inj.mp e)
    rw [h', Function.update_of_ne (Ne.symm h)]
    rfl

/-- A step of `readExpsH`: bump, then count the rest. -/
theorem readExpsH_cons (m : Counts) (a : K) (rest : List K) :
    readExpsH m (a :: rest) =
      (m.get a :: (readExpsH (m.bump a) rest).1, (readExpsH (m.bump a) rest).2) := rfl

/-- A step of `mkRowsH`: number the reads, bump the slot, write the row. -/
theorem mkRowsH_cons (rd : K → Option E) (sm sb : Counts) (sk : Skel) (rest : List Skel)
    (acc : Array PRow) :
    mkRowsH rd sm sb (sk :: rest) acc =
      mkRowsH rd (readExpsH sm (readAddrsBy rd sk.fp sk.ins)).2 (sb.bump sk.pc) rest
        (acc.push ⟨sk, (readExpsH sm (readAddrsBy rd sk.fp sk.ins)).1, sb.get sk.pc⟩) := rfl

/-- The hash-map counters number the reads as `readExps` and leave `readBump`. -/
theorem readExpsH_spec (m : Counts) (l : List K) :
    (readExpsH m l).1 = readExps m.get l ∧ (readExpsH m l).2.get = readBump m.get l := by
  induction l generalizing m with
  | nil => exact ⟨rfl, rfl⟩
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih (m.bump a)
    rw [Counts.get_bump] at h1 h2
    exact ⟨by rw [readExpsH_cons]; simp only [readExps, h1], h2⟩

/-- At the image's reader, the hash-map rows are `mkRows`, and the counters left are the reads'. -/
theorem mkRowsH_spec {κ : ℕ} (mem : MemImage κ) (sm sb : Counts) (S : List Skel)
    (acc : Array PRow) :
    (mkRowsH mem.read sm sb S acc).1.toList = acc.toList ++ mkRows mem sm.get sb.get S ∧
      (mkRowsH mem.read sm sb S acc).2.1.get =
        readBump sm.get (S.flatMap fun sk ↦ readAddrs mem sk.fp sk.ins) ∧
      (mkRowsH mem.read sm sb S acc).2.2.get = readBump sb.get (S.map (·.pc)) := by
  induction S generalizing sm sb acc with
  | nil => exact ⟨by simp [mkRowsH, mkRows], rfl, rfl⟩
  | cons sk S ih =>
    obtain ⟨e1, e2⟩ := readExpsH_spec sm (readAddrs mem sk.fp sk.ins)
    obtain ⟨h1, h2, h3⟩ := ih (readExpsH sm (readAddrs mem sk.fp sk.ins)).2 (sb.bump sk.pc)
      (acc.push ⟨sk, (readExpsH sm (readAddrs mem sk.fp sk.ins)).1, sb.get sk.pc⟩)
    simp only [e2, Counts.get_bump] at h1 h2 h3
    rw [mkRowsH_cons]
    simp only [readAddrsBy_read]
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, mkRows]
      simp [readBump, e1]
    · rw [h2, List.flatMap_cons, readBump_append]
    · rw [h3, List.map_cons]
      rfl

/-! ## The witness at a reader -/

/-- `opRows` at a reader, the counts' powers read from a table of powers. -/
def opRowsBy (P : PowTable) (rd : K → Option E) (R : List PRow) (op : Opcode) :
    List (Array K) :=
  (R.filter fun r ↦ r.sk.ins.opcode = op).map fun r ↦
    rowOfBy rd r.sk.pc r.sk.fp (fun j ↦ P.pow (r.exps.getD j 0)) (P.pow r.bc) r.sk.ins

/-- At the image's reader, the table rows are `opRows`'. -/
theorem opRowsBy_read (P : PowTable) {κ : ℕ} (mem : MemImage κ) (R : List PRow)
    (op : Opcode) : opRowsBy P mem.read R op = opRows mem R op := by
  rw [opRowsBy, opRows, rowOfBy_read]
  congr 1
  funext r
  simp only [PowTable.pow_eq]
  rfl

/-- A memory row's raw row, written out. -/
theorem rawRow_memRow (a b : K) (v : Vector K 3) :
    rawRow (⟨a, b, v⟩ : MemRow K) = #[a, b, v[0], v[1], v[2]] := by
  simp only [rawRow, circuit_norm, toElements]
  simp only [Vector.toArray_cast, Vector.append_empty]
  rcases v with ⟨⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, _ | _⟩⟩⟩⟩, h⟩ <;> simp at h
  rfl

/-- `memRowsOf`, the addresses and the finalize counts read from a table of powers. -/
def memRowsBy (P : PowTable) {κ : ℕ} (img : MemImage κ) (fin : K → ℕ) : List (Array K) :=
  List.ofFn fun i : Fin (2 ^ κ) ↦
    let a := P.pow i
    let w := img i
    #[a, P.pow (fin a), w.limb 0, w.limb 1, w.limb 2]

/-- They are `memRowsOf`. -/
theorem memRowsBy_eq (P : PowTable) {κ : ℕ} (img : MemImage κ) (fin : K → ℕ) :
    memRowsBy P img fin = memRowsOf img fin := by
  unfold memRowsBy memRowsOf
  congr 1
  funext i
  rw [memRowOf, rawRow_memRow]
  simp only [PowTable.pow_eq]
  rfl

/-- The memory block from rows equal to `memRowsOf`'s. -/
def memBlockOf {κ : ℕ} (hκ : κ ≤ maxLogMem) (img : MemImage κ) (fin : K → ℕ)
    (rows : List (Array K)) (h : rows = memRowsOf img fin) : Air.Flat.Table K :=
  tableOf (memComponent κ) rows (h ▸ memRowsOf_width img fin)
    (h ▸ (memRowsOf_length img fin).trans_le
      ((Nat.pow_le_pow_right (by norm_num) (hκ.trans (by decide) : κ ≤ 64)).trans (by decide)))
    (h ▸ memRowsOf_fixed hκ img fin)

/-- It is `memBlock`. -/
theorem memBlockOf_eq {κ : ℕ} (hκ : κ ≤ maxLogMem) (img : MemImage κ) (fin : K → ℕ)
    (rows : List (Array K)) (h : rows = memRowsOf img fin) :
    memBlockOf hκ img fin rows h = memBlock hκ img fin := by
  subst h
  rfl

/-- The table of an opcode from rows equal to `opRows`'. -/
def opTableOf {κ : ℕ} (img : MemImage κ) (R : List PRow) (hR : R.length ≤ UInt64.size)
    (op : Opcode) (rows : List (Array K)) (h : rows = opRows img R op) : Air.Flat.Table K :=
  tableOf (opComponent op) rows (h ▸ opRows_width img R op)
    (h ▸ (opRows_length_le img R op).trans hR) (by cases op <;> exact trivial)

/-- It is `opTable`. -/
theorem opTableOf_eq {κ : ℕ} (img : MemImage κ) (R : List PRow) (hR : R.length ≤ UInt64.size)
    (op : Opcode) (rows : List (Array K)) (h : rows = opRows img R op) :
    opTableOf img R hR op rows h = opTable img R hR op := by
  subst h
  rfl

/-- Opcode tables of equal rows are equal. -/
theorem opTable_congr {κ : ℕ} (img : MemImage κ) {R R' : List PRow} (h : R = R')
    (hR : R.length ≤ UInt64.size) (op : Opcode) :
    opTable img R hR op = opTable img R' (h ▸ hR) op := by
  subst h
  rfl

/-- The hash-map rows at a reader equal to the image's are `padRows`. -/
theorem mkRowsH_rows {κ : ℕ} {img : MemImage κ} {rd : K → Option E} (hrd : rd = img.read)
    (S : List Skel) : (mkRowsH rd ∅ ∅ S #[]).1.toList = padRows img S := by
  subst hrd
  rw [(mkRowsH_spec img ∅ ∅ S #[]).1, Counts.get_empty]
  rfl

/-- A bytecode row's raw row, written out. -/
theorem rawRow_bytecodeRow (a b c : K) (v : Vector K 7) :
    rawRow (⟨a, b, c, v⟩ : BytecodeRow K) =
      #[a, b, c, v[0], v[1], v[2], v[3], v[4], v[5], v[6]] := by
  simp only [rawRow, circuit_norm, toElements]
  simp only [Vector.toArray_cast, Vector.append_empty]
  rw [Vector.toArray_append, Vector.toArray_append, Vector.toArray_append]
  apply Array.ext (by simp)
  intro i _ h
  simp at h
  interval_cases i <;> simp

/-- `bcRowsOf`, the addresses and the finalize counts read from a table of powers. -/
def bcRowsBy (P : PowTable) (prog : Program) (fin : K → ℕ) : List (Array K) :=
  List.ofFn fun i : Fin (2 ^ prog.logSize) ↦
    let a := P.pow i
    let e := entry (prog.code i)
    #[a, P.pow (fin a), e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7]]

/-- They are `bcRowsOf`. -/
theorem bcRowsBy_eq (P : PowTable) (prog : Program) (fin : K → ℕ) :
    bcRowsBy P prog fin = bcRowsOf prog fin := by
  unfold bcRowsBy bcRowsOf
  congr 1
  funext i
  rw [bytecodeRowOf, rawRow_bytecodeRow]
  simp only [PowTable.pow_eq]
  rfl

/-- The bytecode block from rows equal to `bcRowsOf`'s. -/
def bcBlockOf (prog : Program) (fin : K → ℕ) (rows : List (Array K))
    (h : rows = bcRowsOf prog fin) : Air.Flat.Table K :=
  tableOf (bytecodeComponent prog) rows (h ▸ bcRowsOf_width prog fin)
    (h ▸ (bcRowsOf_length prog fin).trans_le
      ((Nat.pow_le_pow_right (by norm_num)
        (prog.logSize_le.trans (by decide) : prog.logSize ≤ 64)).trans (by decide)))
    (h ▸ bcRowsOf_fixed prog fin)

/-- It is `bcBlock`. -/
theorem bcBlockOf_eq (prog : Program) (fin : K → ℕ) (rows : List (Array K))
    (h : rows = bcRowsOf prog fin) : bcBlockOf prog fin rows h = bcBlock prog fin := by
  subst h
  rfl

/-- The eight tables of `padTables` from the hash-map rows `res` of the skeletons at a reader
equal to the image's, the powers read from a table. -/
def padTablesOf (prog : Program) (P : PowTable) {κ : ℕ} (img : MemImage κ) (rd : K → Option E)
    (hrd : rd = img.read) (S : List Skel) (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size)
    (res : Array PRow × Counts × Counts) (hres : res = mkRowsH rd ∅ ∅ S #[]) :
    List (Air.Flat.Table K) :=
  have hRl : res.1.toList.length ≤ UInt64.size := by
    rw [hres, mkRowsH_rows hrd S]
    exact (padRows_length img S).trans_le hS
  have hrows : ∀ op, opRowsBy P rd res.1.toList op = opRows img res.1.toList op := fun op ↦ by
    rw [hrd, opRowsBy_read]
  [opTableOf img res.1.toList hRl .xor (opRowsBy P rd res.1.toList .xor) (hrows _),
    opTableOf img res.1.toList hRl .mulNative (opRowsBy P rd res.1.toList .mulNative) (hrows _),
    opTableOf img res.1.toList hRl .setConstant (opRowsBy P rd res.1.toList .setConstant)
      (hrows _),
    opTableOf img res.1.toList hRl .deref (opRowsBy P rd res.1.toList .deref) (hrows _),
    opTableOf img res.1.toList hRl .jump (opRowsBy P rd res.1.toList .jump) (hrows _),
    opTableOf img res.1.toList hRl .blake2s (opRowsBy P rd res.1.toList .blake2s) (hrows _),
    memBlockOf hκ img res.2.1.get (memRowsBy P img res.2.1.get) (memRowsBy_eq P img _),
    bcBlockOf prog res.2.2.get (bcRowsBy P prog res.2.2.get) (bcRowsBy_eq P prog _)]

/-- The eight tables of `padTables`, computed at a reader equal to the image's. -/
def padTablesBy (prog : Program) (P : PowTable) {κ : ℕ} (img : MemImage κ) (rd : K → Option E)
    (hrd : rd = img.read) (S : List Skel) (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size) :
    List (Air.Flat.Table K) :=
  padTablesOf prog P img rd hrd S hκ hS (mkRowsH rd ∅ ∅ S #[]) rfl

/-- The computed tables are `padTables`. -/
theorem padTablesBy_eq (prog : Program) (P : PowTable) {κ : ℕ} (img : MemImage κ)
    (rd : K → Option E) (hrd : rd = img.read) (S : List Skel) (hκ : κ ≤ maxLogMem)
    (hS : S.length ≤ UInt64.size) :
    padTablesBy prog P img rd hrd S hκ hS = padTables prog img S hκ hS := by
  have hm : (mkRowsH rd ∅ ∅ S #[]).2.1.get = padMemFin img S := by
    subst hrd
    rw [(mkRowsH_spec img ∅ ∅ S #[]).2.1, Counts.get_empty]
    rfl
  have hb : (mkRowsH rd ∅ ∅ S #[]).2.2.get = padBcFin S := by
    subst hrd
    rw [(mkRowsH_spec img ∅ ∅ S #[]).2.2, Counts.get_empty]
    rfl
  simp only [padTablesBy, padTablesOf, opTableOf_eq, memBlockOf_eq, bcBlockOf_eq, padTables, hm,
    hb, opTable_congr img (mkRowsH_rows hrd S)]

/-- Witnesses of equal tables are equal. -/
theorem witnessOfTables_congr {prog : Program} {κ : ℕ} {pi : PublicIO K}
    {ts ts' : List (Air.Flat.Table K)} (h : ts = ts')
    (hc : ts.map (·.component) = (leanIsaEnsemble prog κ).tables)
    (hc' : ts'.map (·.component) = (leanIsaEnsemble prog κ).tables) :
    witnessOfTables prog κ pi ts hc = witnessOfTables prog κ pi ts' hc' := by
  subst h
  rfl

/-- `padWitness`, computed at a reader equal to the image's. -/
def padWitnessBy (prog : Program) (input : PublicInput) (P : PowTable) {κ : ℕ}
    (img : MemImage κ) (rd : K → Option E) (hrd : rd = img.read) (S : List Skel)
    (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size) :
    EnsembleWitness (leanIsaEnsemble prog κ) :=
  witnessOfTables prog κ (PublicIO.ofInput input) (padTablesBy prog P img rd hrd S hκ hS)
    ((congrArg _ (padTablesBy_eq prog P img rd hrd S hκ hS)).trans
      (padTables_components prog img S hκ hS))

/-- **The computed witness is `padWitness`.** -/
theorem padWitnessBy_eq (prog : Program) (input : PublicInput) (P : PowTable) {κ : ℕ}
    (img : MemImage κ) (rd : K → Option E) (hrd : rd = img.read) (S : List Skel)
    (hκ : κ ≤ maxLogMem) (hS : S.length ≤ UInt64.size) :
    padWitnessBy prog input P img rd hrd S hκ hS = padWitness prog input img S hκ hS :=
  witnessOfTables_congr (padTablesBy_eq prog P img rd hrd S hκ hS) _ _

/-! ## The run's skeletons -/

section Run

variable {prog : Program} {t : Trace prog}

/-- Stepping forward from step `k` collects the skeletons of the steps `k, k + 1, …`. -/
theorem runSkelsBy_stateAt (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog))
    {fetch : K → Option Instr} (hf : fetch = prog.fetch)
    {exec : Regs K → Instr → Option (Regs K)} (he : exec = execute t.image) :
    ∀ n k (acc : Array Skel), k + n = t.steps →
      (runSkelsBy fetch exec n (stateAt t k) acc).toList =
        acc.toList ++ (List.range' k n).map (skAt t) := by
  subst hf he
  intro n
  induction n with
  | zero => intro k acc _; simp [runSkelsBy]
  | succ n ih =>
    intro k acc hk
    obtain ⟨ins, hfi, hex⟩ := stateAt_exec hv (show k < t.steps by omega)
    have hsk : skAt t k = ⟨(stateAt t k).pc, (stateAt t k).fp, ins⟩ := by
      simp only [skAt, hfi, Option.getD_some]
    simp only [runSkelsBy, hfi, hex]
    rw [ih (k + 1) _ (by omega), List.range'_succ, List.map_cons, hsk]
    simp

/-- **The forward pass collects the run's skeletons.** -/
theorem runSkelsBy_eq_runSkels
    (hv : run prog t.image t.steps Regs.initial = some (Regs.final prog))
    {fetch : K → Option Instr} (hf : fetch = prog.fetch)
    {exec : Regs K → Instr → Option (Regs K)} (he : exec = execute t.image) :
    (runSkelsBy fetch exec t.steps Regs.initial #[]).toList = t.runSkels := by
  have h := runSkelsBy_stateAt hv hf he t.steps 0 #[] (Nat.zero_add _)
  rw [runSkels_eq hv, List.range_eq_range']
  exact h

end Run

/-! ## The generator -/

/-- The witness of the skeletons `S` over the image padded at the fill starts `pcs`, read through
the table of powers `P`; `none` when the padded memory or the skeletons exceed the caps. -/
def witnessAt (prog : Program) (input : PublicInput) (t : Trace prog) (pcs : Opcode → ℕ → ℕ)
    (P : PowTable) (S : List Skel) :
    Option (EnsembleWitness (leanIsaEnsemble prog (t.κ + 1))) :=
  if hκ : t.κ + 1 ≤ maxLogMem then
    if hS : S.length ≤ UInt64.size then
      some (padWitnessBy prog input P (padImage t.image pcs) (readBy (padImage t.image pcs) P)
        (funext (readBy_eq_read (by unfold maxLogMem at hκ; omega) _ P)) S hκ hS)
    else none
  else none

/-- **The witness generator.** Search the fill starts and pad the image; step the run forward
once and count its rows per table; search the `JUMP` exponent; append the fill's skeletons; write
the tables. Addresses are read through one table of powers, checked on every read. -/
def witnessGen (prog : Program) (input : PublicInput) (t : Trace prog) :
    Option (EnsembleWitness (leanIsaEnsemble prog (t.κ + 1))) :=
  let pcs := startsOf (fillStartTable prog)
  let P := powTable (2 ^ max (t.κ + 1) prog.logSize)
  let runS := (runSkelsBy (fetchBy prog P) (executeWith (readBy t.image P)) t.steps
    Regs.initial #[]).toList
  let rows := countsOf (skelCountTable runS)
  match jumpHeight (jumpOwed rows) with
  | none => none
  | some τ => witnessAt prog input t pcs P (runS ++ padSkels t.κ pcs (planCount rows τ))

/-- **Correctness of the witness generator**. On well-formed bytecode, every valid
execution that fits gets a witness, which satisfies the constraint statement and represents the
trace padded at the searched fill starts. -/
theorem witnessGen_correct {prog : Program} {input : PublicInput} {t : Trace prog}
    (hwf : WellFormedBytecode prog) (h : ValidExecution prog input t) (hfit : t.Fits) :
    ∃ w, witnessGen prog input t = some w ∧ SatisfiedBy prog input w ∧
      AssignmentRepresents w (padTrace t (fillStarts prog)) := by
  have hκ64 : t.κ < 64 := lt_of_le_of_lt h.1.2.1 (by decide)
  have hrun : ∀ P, (runSkelsBy (fetchBy prog P) (executeWith (readBy t.image P))
      t.steps Regs.initial #[]).toList = t.runSkels := fun P ↦
    runSkelsBy_eq_runSkels h.2 (funext (fetchBy_eq_fetch prog P))
      (executeWith_readBy hκ64 t.image P)
  have hrows : countsOf (skelCountTable t.runSkels) = t.runRows := by
    rw [countsOf_skelCountTable]
    funext op
    exact t.count_runSkels op
  obtain ⟨τ, hτeq⟩ := Option.isSome_iff_exists.mp (jumpHeight_isSome hfit.jump)
  obtain ⟨hτ, h1, h2⟩ := jumpHeight_spec hτeq
  have hcap : (padTrace t (fillStarts prog)).κ ≤ maxLogMem := hfit.room
  have hlen := padSkelsOf_length_le (pcs := fillStarts prog) hτ h1 h2 hfit
  refine ⟨_, ?_, padWitness_complete (fillStarts_spec hwf.hasFillBlocks) hτ h1 h2 h hfit hcap
    hlen⟩
  simp only [witnessGen, hrun, hrows]
  rw [show jumpOwed t.runRows = t.owed from rfl, hτeq]
  have hcap' : t.κ + 1 ≤ maxLogMem := hcap
  have hlen' : (t.runSkels ++ padSkels t.κ (startsOf (fillStartTable prog))
      (planCount t.runRows τ)).length ≤ UInt64.size := hlen
  simp only [witnessAt]
  rw [dite_eq_left hcap', dite_eq_left hlen']
  exact congrArg some (padWitnessBy_eq _ _ _ _ _ _ _ _ _)

/-- An opcode table of the padded witness has a row per skeleton of its opcode. -/
theorem padWitness_opLength {prog : Program} {input : PublicInput} {κ : ℕ} {img : MemImage κ}
    {S : List Skel} {hκ : κ ≤ maxLogMem} {hS : S.length ≤ UInt64.size} (j : Fin 6) :
    (tableAt (padWitness prog input img S hκ hS) ⟨j, by omega⟩).table.length =
      Skel.count (fillTables.getD j .xor) S := by
  rw [(padWitness_tableAt _).2]
  fin_cases j <;> exact opRows_length img S _

/-- **The heights of the generated tables.** On a valid execution, the generator's `JUMP`
exponent is `jumpHeight t.owed`, and opcode table `j` of its witness has `tableHeight` rows: the
target of its run rows, `2^τ` for `JUMP`. -/
theorem witnessGen_heights {prog : Program} {input : PublicInput} {t : Trace prog}
    {w : EnsembleWitness (leanIsaEnsemble prog (t.κ + 1))}
    (h : ValidExecution prog input t) (hw : witnessGen prog input t = some w) :
    ∃ τ, jumpHeight t.owed = some τ ∧ ∀ j : Fin 6,
      (tableAt w ⟨j, by omega⟩).table.length =
        tableHeight t.runRows τ (fillTables.getD j .xor) := by
  have hκ64 : t.κ < 64 := lt_of_le_of_lt h.1.2.1 (by decide)
  have hrun : ∀ P, (runSkelsBy (fetchBy prog P) (executeWith (readBy t.image P))
      t.steps Regs.initial #[]).toList = t.runSkels := fun P ↦
    runSkelsBy_eq_runSkels h.2 (funext (fetchBy_eq_fetch prog P))
      (executeWith_readBy hκ64 t.image P)
  have hrows : countsOf (skelCountTable t.runSkels) = t.runRows := by
    rw [countsOf_skelCountTable]
    funext op
    exact t.count_runSkels op
  simp only [witnessGen, hrun, hrows] at hw
  rw [show jumpOwed t.runRows = t.owed from rfl] at hw
  rcases hτ : jumpHeight t.owed with _ | τ
  · rw [hτ] at hw
    cases hw
  rw [hτ] at hw
  obtain ⟨-, h1, h2⟩ := jumpHeight_spec hτ
  refine ⟨τ, rfl, fun j ↦ ?_⟩
  simp only [witnessAt] at hw
  split_ifs at hw with hκ hS
  obtain rfl := Option.some.inj hw
  rw [padWitnessBy_eq, padWitness_opLength, Trace.count_rows t t.κ _ h1 h2]

end LeanerVM.Arithmetization
