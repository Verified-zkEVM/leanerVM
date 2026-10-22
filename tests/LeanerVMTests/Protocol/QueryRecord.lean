import LeanerVM.Protocol.ToArkLib.QueryRecord
import LeanerVM.Protocol.ToArkLib.SendOracleBeside

/-!
# Query-record and send-oracle-beside tests

The two generic components of the WHIR opening on a toy: the oracle is a table `Fin 4 → ℕ`, the
statement a position. A plain file, so `#guard` evaluates the compiled definitions.

* **Query-record** asks the oracle at the statement's position, rejects on a zero answer, and
  records the answer in the output statement: the guarded form's check and verdict are the
  question's answer, and the oracles handed on are the ones `keep` selects (all of them for the
  identity, only the message for the one beside).
* **Send-oracle-beside** sends the prover's message beside the input oracle: the output family
  is the input at `inl` and the message at `inr`.
* Each fails when what it is built from changes: a zero answer is rejected, the record follows
  the table, and the oracle handed on after the drop is the message and not the input.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Protocol Component OracleComp OracleSpec ProtocolSpec

/-- A table of four numbers, queried by position. -/
abbrev Tab := Fin 4 → ℕ

/-- One table as the oracles. -/
abbrev OneTab : Fin 1 → Type := fun _ ↦ Tab

/-- The question: the statement's position of the one oracle. -/
def toyQuery (s : Fin 4) : [OneTab]ₒ.Domain := ⟨0, s⟩

/-- The answer, as a number. -/
def num {s : Fin 4} (a : [OneTab]ₒ.Range (toyQuery s)) : ℕ := a

/-- The check: the answer is nonzero. -/
def toyCheck (s : Fin 4) (a : [OneTab]ₒ.Range (toyQuery s)) : Bool := decide (num a ≠ 0)

/-- The output statement: the answer and the position. -/
def toyOut (s : Fin 4) (a : [OneTab]ₒ.Range (toyQuery s)) : ℕ := 10 * num a + s.val

/-- The identity injection of the one oracle. -/
abbrev keepOne : Fin 1 ↪ Fin 1 := Function.Embedding.refl (Fin 1)

/-- The component, keeping the one oracle. -/
def toyRecord : Def (Fin 4) OneTab Unit ℕ (keptOracles OneTab keepOne) Unit !p[] :=
  queryRecord OneTab keepOne toyQuery toyCheck toyOut

/-- A table with a zero at position 2. -/
def tab : Tab := ![5, 7, 0, 3]

/-- The oracle data: the table. -/
def oracles : ∀ i, OneTab i := fun _ ↦ tab

/-- The guarded form of the toy. -/
abbrev toyGuarded := queryRecordGuarded OneTab keepOne toyQuery toyCheck toyOut

/-! ## Query-record -/

-- the answer the oracles give
#guard num (answerOf OneTab oracles (toyQuery 1)) = 7

-- the check on a nonzero answer passes and the verdict records it
#guard toyGuarded.check (1, oracles) (fun i ↦ Fin.elim0 i) = true
#guard (toyGuarded.out (1, oracles) (fun i ↦ Fin.elim0 i)).1 = 71

-- a zero answer is rejected: the check is load-bearing
#guard toyGuarded.check (2, oracles) (fun i ↦ Fin.elim0 i) = false

-- the record follows the table: another table, another verdict
#guard (toyGuarded.out (1, fun _ ↦ ![5, 9, 0, 3]) (fun i ↦ Fin.elim0 i)).1 = 91

-- the oracles handed on are the input
#guard (toyGuarded.out (1, oracles) (fun i ↦ Fin.elim0 i)).2 0 2 = 0

/-- The answer is the table's entry. -/
theorem num_answerOf (o : ∀ i, OneTab i) (s : Fin 4) :
    num (answerOf OneTab o (toyQuery s)) = o 0 s := rfl

/-- Completeness, applied: on tables nonzero at the position the check passes and the recorded
answer is nonzero. -/
def toyComplete :
    Complete toyRecord {p | p.1.2 0 p.1.1 ≠ 0} {p | p.1.1 / 10 ≠ 0} :=
  queryRecordComplete OneTab keepOne toyQuery toyCheck toyOut fun s o w h ↦ by
    have h' : o 0 s ≠ 0 := h
    refine ⟨?_, ?_⟩
    · simp only [toyCheck, num_answerOf]
      exact decide_eq_true h'
    · have hs := s.isLt
      show (toyOut s (answerOf OneTab o (toyQuery s))) / 10 ≠ 0
      unfold toyOut
      rw [num_answerOf]
      omega

/-! ## Send-oracle-beside, then a query-record that hands on the message only -/

/-- The prover's message: the input table plus one. -/
def toyMessage (p : (Fin 4 × ∀ i, OneTab i) × Unit) : Tab := fun j ↦ p.1.2 0 j + 1

/-- The component: the message beside the input table. -/
def toyBeside : Def (Fin 4) OneTab Unit (Fin 4) (besideOracles OneTab Tab) Unit (sayO Tab) :=
  sendOracleBeside OneTab Tab toyMessage _root_.id

#guard (besideData OneTab Tab oracles (toyMessage ((1, oracles), ())) (.inl 0) : Tab) 1 = 7
#guard (besideData OneTab Tab oracles (toyMessage ((1, oracles), ())) (.inr ()) : Tab) 1 = 8

/-- The inclusion of the message in the beside family. -/
def keepMessage : Fin 1 ↪ Fin 1 ⊕ Unit :=
  ⟨fun _ ↦ .inr (), fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- The answer of the beside family's first oracle, as a number. -/
def numB {s : Fin 4}
    (a : [besideOracles OneTab Tab]ₒ.Range
      (⟨.inl 0, s⟩ : [besideOracles OneTab Tab]ₒ.Domain)) : ℕ := a

/-- The drop: ask the old table, record, hand on the message. -/
def dropQuery (s : Fin 4) : [besideOracles OneTab Tab]ₒ.Domain := ⟨.inl 0, s⟩
def dropCheck (s : Fin 4) (a : [besideOracles OneTab Tab]ₒ.Range (dropQuery s)) : Bool :=
  decide (numB (s := s) a ≠ 0)
def dropOut (s : Fin 4) (a : [besideOracles OneTab Tab]ₒ.Range (dropQuery s)) : ℕ :=
  10 * numB (s := s) a + s.val

/-- Ask the input table, hand on the message: the old table is dropped. -/
def toyDrop : Def (Fin 4) (besideOracles OneTab Tab) Unit ℕ
    (keptOracles (besideOracles OneTab Tab) keepMessage) Unit !p[] :=
  queryRecord (besideOracles OneTab Tab) keepMessage dropQuery dropCheck dropOut

/-- The data after the commit: the input table and the message. -/
def beside : ∀ i, besideOracles OneTab Tab i :=
  besideData OneTab Tab oracles (toyMessage ((1, oracles), ()))

/-- The guarded form of the drop. -/
abbrev dropGuarded :=
  queryRecordGuarded (besideOracles OneTab Tab) keepMessage dropQuery dropCheck dropOut

-- the drop reads the old table (7 at position 1) and keeps the message (8 at position 1)
#guard (dropGuarded.out (1, beside) (fun i ↦ Fin.elim0 i)).1 = 71
#guard (dropGuarded.out (1, beside) (fun i ↦ Fin.elim0 i)).2 0 1 = 8

end LeanerVMTests.Protocol
