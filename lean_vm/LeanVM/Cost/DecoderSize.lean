module

public import LeanVM.Cost.DecoderProgram
public import LeanVM.Cost.Decoder.Top
public import LeanVM.Cost.DecoderSize.Locs

/-!
# The guest decoder's program: its indices and its size, by evaluation

A firewall (`AGENTS.md`), as `Cost/ExtractorSize.lean` is the extractor's: the kernel evaluations
over the decoder program's bodies, in a module of their own that imports only the program's
definition with its facts, the compiled top and the row chunks, none of the proofs that use these
evaluations, so that no edit of those proofs rebuilds them. Through the program's definition and the
compiled top it imports what the compiled chain imports (`Guest/Located/Replay.lean`,
`Guest/B1/Main/Interface.lean`, the extractor's `Cost/Extractor/Top.lean`), not the proofs that use
them. For the program `decoderProgramOf j deps` (`Cost/DecoderProgram.lean`) of a compiled top `j`
with its bodies `deps`:

* the indices increase from the entry's `0` (`increasingFrom 0 (deps.map (·.1))`, by
  `decide +kernel`): the program holds its bodies and its entry (`decoderProgramOf_includes`,
  `decoderProgramOf_entry`);
* its size is exactly the bodies' sizes and two per index without a body (a literal `0`), the
  indices being distinct (`size_ofList_add_length`, `decoderProgramOf_size_le_of_increasing`): at
  most a measured number, then `guestDecoderSizeBound`. The guest's frame cells' literal
  (`guestLocsTableC`, `749836`: the table's `749835` and one for its `Term.val` node) is measured by
  chunks of rows, each evaluation in a module of its own (`DecoderSize/Rows*.lean`, `Names*.lean`,
  summed in `DecoderSize/Locs.lean`: one evaluation of the whole table takes over `18` GB), its body
  picked out by its index (`decoderProgramBodies_filter_locs`, by unfolding); the other bodies'
  sizes by `decide +kernel`, which reads the literal's index alone.

For the compiled top `decTopC` (`Decoder/Top.lean`): at most the bodies' sizes (`784277`: the frame
cells' `749836` and the others', the entry's among them, `34441`, each exact) plus two per index
without a body, the indices up to the top's, `decTopC`'s own (the last index allocated), less the
bodies (`costIdx - costDeps.length`; so the bound names no index, which moves when a module before
it in the chain gains a function): `785159` at index `848` with `407` bodies besides the entry, the
program's exact size (`LeanVMTests/Cost/DecoderSize.lean`), of which the guest's frame cells
(`guestLocs`, a literal held once, `guestLocsTable`) are `749835`. `guestDecoderSizeBound`
(`Statement/Theorems.lean`) is `785500`: this exact size and a slack of `341`, room for one leanXMSS
signature's encoding (`309`) but not two. The bound applies to every program, but its slack is small
only for programs written like this one: the frame cells (below `2^20` each), packed three to a
limb, would take about a third of their `749835`, freeing room for about `1600` signatures'
encodings. -/

namespace LeanVM.Cost

open LeanVM.Cost.Decoder

public section

/-- The bodies' indices increase from the entry's `0`. -/
theorem decoderProgram_indices_increasing :
    increasingFrom 0 (decTopC.costDeps.map (·.1)) = true := by
  decide +kernel

/-- **The guest's frame cells' literal**: its size, its rows' (`guestLocsList_rowSize`, the
chunks of `DecoderSize/Locs.lean`), the array's and `Term.val`'s. -/
theorem guestLocsTable_size : guestLocsTableC.costBody.size = 749836 := by
  have h : guestLocsTableC.costBody = Term.val (MachineValue.arr
      (guestLocsList.map fun r ↦ MachineValue.arr (r.map encodeValue).toArray).toArray) := rfl
  rw [h, literal_size, guestLocsList_rowSize]

/-- The sum of a function over a list: over the entries `p` keeps and over the others. -/
theorem sum_map_filter_add {α : Type} (f : α → ℕ) (p : α → Bool) (l : List α) :
    (l.map f).sum = ((l.filter p).map f).sum + ((l.filter fun x ↦ !p x).map f).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => cases h : p x <;> simp [h, ih] <;> omega

set_option maxRecDepth 100000 in
/-- The literal's body is the bodies' one at its index (by unfolding: no body is evaluated). -/
theorem decoderProgramBodies_filter_locs :
    (decoderProgramBodiesOf decTopC.costIdx decTopC.costDeps).filter
        (fun p ↦ p.1 == guestLocsTableC.costIdx) =
      [(guestLocsTableC.costIdx, guestLocsTableC.costBody)] := by
  rfl

/-- The bound of `size_ofList_add_length` on bodies `L`, from one body's size at index `i` and
the others', with `d + 1` bodies up to index `k`: their sizes and two per index without a body.
Stated for any list: on the program's bodies, a ground term, `rw` and `omega` would evaluate
them. -/
theorem bodies_size_bound_of_split (L : List (ℕ × Term)) (i k n r s d : ℕ) (b : Term)
    (hf : L.filter (fun p ↦ p.1 == i) = [(i, b)]) (hb : b.size = n)
    (hrest : ((L.filter fun p ↦ !(p.1 == i)).map fun p ↦ p.2.size).sum ≤ r)
    (hmax : (L.map (·.1)).foldr max 0 = k) (hs : n + r = s) (hd : d ≤ k) :
    (L.map fun p ↦ p.2.size).sum + 2 * ((L.map (·.1)).foldr max 0 + 1) ≤
      s + 2 * (k - d) + 2 * (d + 1) := by
  rw [sum_map_filter_add _ (fun p ↦ p.1 == i), hf, hmax, List.map_singleton, List.sum_singleton,
    hb]
  omega

/-- **The program's size**, evaluated: the bodies' sizes, the frame cells' literal
(`guestLocsTable_size`) and the others (`decide`, which reads the literal's index alone), and two
per index without a body: the indices up to the top's, `decTopC.costIdx + 1`, less the bodies,
the entry and `decTopC.costDeps`. -/
theorem decoderProgram_size_le_measured :
    (decoderProgramOf decTopC.costIdx decTopC.costDeps).size ≤
      784277 + 2 * (decTopC.costIdx - decTopC.costDeps.length) :=
  decoderProgramOf_size_le_of_increasing decoderProgram_indices_increasing
    (bodies_size_bound_of_split _ guestLocsTableC.costIdx decTopC.costIdx 749836 34441 784277
      decTopC.costDeps.length _ decoderProgramBodies_filter_locs guestLocsTable_size
      (by decide +kernel) (by decide +kernel) rfl (by decide +kernel))

end

end LeanVM.Cost
