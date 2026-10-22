import LeanerVM.Protocol.ToArkLib.PassCheck

/-!
# Pass-check tests

The component with no round that rejects unless the statement passes a check, on a toy: the
statement is a number, the check is that it is nonzero, the output is its successor, the oracle a
table. A plain file, so `#guard` evaluates the compiled definitions.

* **The guarded form's check and verdict** are the check and the mapped statement, with the
  oracles kept.
* **A statement that fails the check is rejected**: the check is load-bearing.
* **Completeness, applied**: on nonzero statements the check passes and the successor is
  positive.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Protocol Component OracleComp OracleSpec ProtocolSpec

/-- The oracle: a table of two numbers. -/
abbrev PcOracle : Fin 1 → Type := fun _ ↦ Fin 2 → ℕ

/-- The component: the statement must be nonzero, and is replaced by its successor. -/
def pcToy : Def ℕ PcOracle Unit ℕ PcOracle Unit !p[] :=
  passCheck PcOracle (fun s ↦ decide (s ≠ 0)) (fun s ↦ s + 1)

/-- The oracle data. -/
def pcOracles : ∀ i, PcOracle i := fun _ ↦ ![4, 9]

/-- The guarded form of the toy. -/
abbrev pcGuarded := passCheckGuarded PcOracle (fun s : ℕ ↦ decide (s ≠ 0)) (fun s ↦ s + 1)

-- a nonzero statement passes and is mapped
#guard pcGuarded.check (3, pcOracles) (fun i ↦ Fin.elim0 i) = true
#guard (pcGuarded.out (3, pcOracles) (fun i ↦ Fin.elim0 i)).1 = 4

-- a zero statement is rejected
#guard pcGuarded.check (0, pcOracles) (fun i ↦ Fin.elim0 i) = false

-- the oracles are handed on
#guard (pcGuarded.out (3, pcOracles) (fun i ↦ Fin.elim0 i)).2 0 1 = 9

/-- Completeness, applied: on nonzero statements the check passes and the successor is
positive. -/
def pcComplete : Complete pcToy {p | p.1.1 ≠ 0} {p | 0 < p.1.1} :=
  passCheckComplete PcOracle _ _ fun s _ _ h ↦ ⟨decide_eq_true h, Nat.succ_pos s⟩

/-- Security, applied: a statement that passes the check is nonzero. -/
def pcSecurity :
    Security pcToy {p | p.1.1 ≠ 0} {p | 0 < p.1.1} (fun i ↦ Fin.elim0 i.1) :=
  passCheckSecurity PcOracle _ _ fun s _ _ hc _ ↦ by simpa using hc

end LeanerVMTests.Protocol
