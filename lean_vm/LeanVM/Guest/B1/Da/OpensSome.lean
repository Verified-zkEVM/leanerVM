/-
  LeanVM.Guest.B1.Da.OpensSome

  The DA claim over a hash that answers every input: `Witness.OpensWith` at the deployed hash and
  the deployed padding digests is `Witness.Opens` (package W2-S).
-/

module

public import LeanVM.Spec.DaWith

/-!
# The DA opening over a hash that answers everything

`Spec/DaWith.lean` transcribes LeanDA's commitment and vector digest in any monad and recovers
the deployed ones at `Id` (`commitCodewordsWith_id`, `vectorDigestWith_id`). Over `Option` with a
hash answering every input, `fun x ↦ some (f x)`, each is `some` of its `Id` run
(`commitCodewordsWith_some`, `vectorDigestWith_some`); at BLAKE2s and the deployed padding digests
`Witness.OpensWith` is `Witness.Opens` (`opensWith_some_iff`), the DA bridge of package W2-S
(`docs/roadmap/w2-guest-model.md`).
-/

namespace LeanVM.Da

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash

@[expose] public section

section Some

variable (H : List UInt8 → LeanDa.Digest)

/-- A `mapM` over `Option` whose every step is answered is `some` of the map. -/
theorem mapM_option_some {α β : Type} (f : α → Option β) (g : α → β) (hf : ∀ a, f a = some (g a)) :
    ∀ l : List α, l.mapM f = some (l.map g)
  | [] => rfl
  | a :: l => by
    rw [List.mapM_cons, hf a, mapM_option_some f g hf l]
    rfl

/-- A cell's digest over a hash answering everything. -/
theorem listCellDigestWith_some (row : List K) (j : ℕ) :
    listCellDigestWith (m := Option) (fun x ↦ some (H x)) row j =
      some (Id.run (listCellDigestWith (m := Id) H row j)) := rfl

/-- A row's digest over a hash answering everything. -/
theorem rowDigestWith_some (row : List K) :
    rowDigestWith (m := Option) (fun x ↦ some (H x)) row =
      some (Id.run (rowDigestWith (m := Id) H row)) := by
  simp only [rowDigestWith]
  rw [mapM_option_some _ (fun j ↦ Id.run (listCellDigestWith (m := Id) H row j))
    (fun j ↦ listCellDigestWith_some H row j)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  show some _ = some (Id.run (do
    let ds ← (List.range LeanDa.payloadCells).mapM (m := Id) fun j ↦ listCellDigestWith H row j
    H (ds.flatMap fun d ↦ d.toList)))
  rw [mapM_id]
  rfl

/-- A tree level over a hash answering everything. -/
theorem treeLevelWith_some (nodes : List LeanDa.Digest) :
    treeLevelWith (m := Option) (fun x ↦ some (H x)) nodes =
      some (Id.run (treeLevelWith (m := Id) H nodes)) := by
  simp only [treeLevelWith]
  rw [mapM_option_some _ _ (fun _ ↦ rfl), mapM_id]
  rfl

/-- A tree's root over a hash answering everything, at any fuel. -/
theorem treeRootFuel_some : ∀ (fuel : ℕ) (nodes : List LeanDa.Digest),
    treeRootFuel (m := Option) (fun x ↦ some (H x)) fuel nodes =
      some (Id.run (treeRootFuel (m := Id) H fuel nodes))
  | 0, _ => rfl
  | fuel + 1, nodes => by
    rw [treeRootFuel, treeRootFuel]
    split
    · rfl
    · rw [treeLevelWith_some]
      simp only [Option.bind_eq_bind, Option.bind_some]
      exact treeRootFuel_some fuel _

/-- A tree's root over a hash answering everything. -/
theorem treeRootWith_some (nodes : List LeanDa.Digest) :
    treeRootWith (m := Option) (fun x ↦ some (H x)) nodes =
      some (Id.run (treeRootWith (m := Id) H nodes)) :=
  treeRootFuel_some H _ nodes

/-- **The commitment over a hash answering everything** is `some` of its `Id` run. -/
theorem commitCodewordsWith_some (pc pr : LeanDa.Digest) (rows : List (List K)) :
    commitCodewordsWith (m := Option) (fun x ↦ some (H x)) pc pr rows =
      some (Id.run (commitCodewordsWith (m := Id) H pc pr rows)) := by
  simp only [commitCodewordsWith]
  rw [mapM_option_some _ (fun row ↦ Id.run (rowDigestWith (m := Id) H row))
      (rowDigestWith_some H)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [treeRootWith_some]
  simp only [Option.bind_some]
  rw [mapM_option_some _ (fun ij ↦ if h : ij.1 < rows.length then
      Id.run (listCellDigestWith (m := Id) H rows[ij.1] ij.2) else pc) (fun ij ↦ by
    split <;> rfl)]
  simp only [Option.bind_some]
  rw [treeRootWith_some]
  simp only [Option.bind_some]
  rw [mapM_id, mapM_id]
  rfl

/-- **The vector digest over a hash answering everything** is `some` of its `Id` run. -/
theorem vectorDigestWith_some (vector : List E) :
    vectorDigestWith (m := Option) (fun x ↦ some (H x)) vector =
      some (Id.run (vectorDigestWith (m := Id) H vector)) := rfl

end Some

/-- LeanDA's view of the deployed hash, answering everything, is `some` of `blake2s`. -/
theorem daHash_some :
    daHash (m := Option) (fun x ↦ some (blake2sBytes x)) = fun x ↦ some (blake2s x) := rfl

/-- **The DA bridge** (package W2-S): at BLAKE2s answering every input and the deployed padding
digests, `Witness.OpensWith` is `Witness.Opens`. -/
theorem opensWith_some_iff (root vd : Digest) (w : Witness) :
    w.OpensWith (fun x ↦ some (blake2sBytes x)) (LeanDa.paddingCell blake2s)
        (LeanDa.paddingRow blake2s) root vd ↔ w.Opens root vd := by
  simp only [Witness.OpensWith, Witness.Opens, daHash_some, commitCodewordsWith_some,
    vectorDigestWith_some, commitCodewordsWith_id, vectorDigestWith_id, Option.some.injEq]

end
end LeanVM.Da
