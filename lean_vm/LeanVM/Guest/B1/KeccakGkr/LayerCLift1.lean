/-
  LeanVM.Guest.B1.KeccakGkr.LayerCLift1

  `keccak_layer`'s placement facts, by kernel evaluation: its body a flat list then its return,
  its buffers, its calls, and the pointers its loads go through.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCG
public import LeanVM.Guest.B1.KeccakGkr.FlatF

/-!
# A layer's placement facts

`layerPre first odd`: the body but its return (`layerT_pre`); it is flat (`layerPre_flat`), places
no run (`layerPre_addrs`), allocates the pack challenges (`y` words), the round records (`128`),
the local point (`11`), the next claim's lanes (`25`) and slices (`64`) (`layerPre_alloc`), calls
the pack loop and with `odd` the last round (`layerPre_calls`), and loads only through the
pointers `layerGroups` below their bounds (`layerPre_loads`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory

@[expose] public section

/-- The body but its return. -/
def layerPre (first odd : ℕ) : List Stmt :=
  secA1 first ++ (secA2 first ++ (rmfeBlockT ++ (hornerS first ++ (packSetupT first odd ++
    (lastT (4 * odd) ++ (localS (4 * odd) ++ (tReadsT (4 * odd) ++ (eqfS (4 * odd) ++
      (weightT first (4 * odd) ++ tailPre (4 * odd) (weightEnd first (4 * odd))
        (weightVal first (4 * odd)))))))))))

/-- The returned values. -/
def layerVs (first odd : ℕ) : List V :=
  [.n (weightEnd first (4 * odd) + 279), .n (weightEnd first (4 * odd) + 280),
    .n (weightEnd first (4 * odd) + 281), .n (weightEnd first (4 * odd) + 282),
    .n (weightEnd first (4 * odd) + 283), .n (weightEnd first (4 * odd) + 286)]

theorem layerT_pre (first odd : ℕ) : layerT first odd = layerPre first odd ++ [.ret (layerVs first odd)] := by
  rw [layerT_sections, tailT_split]
  simp only [layerPre, layerVs, List.append_assoc]

theorem layer_fn {first odd : ℕ} (hf : first < 2) (ho : odd < 2) :
    ∃ fn, coreProgram.find? (layerName first odd) = some fn ∧ fn.body = layerT first odd ∧
      fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12,
        .n 13] := by
  interval_cases first <;> interval_cases odd
  · exact ⟨_, find_layer256, layer_body256, rfl⟩
  · exact ⟨_, find_layer257, layer_body257, rfl⟩
  · exact ⟨_, find_layer254, layer_body254, rfl⟩
  · exact ⟨_, find_layer255, layer_body255, rfl⟩

theorem layer_loop {first odd : ℕ} (hf : first < 2) (ho : odd < 2) :
    coreProgram.loop (layerName first odd) = false := by
  interval_cases first <;> interval_cases odd <;> decide +kernel

/-- A dispatch. -/
def dispB : Stmt → Bool
  | .dispatch .. => true
  | _ => false

/-- The pointers the body loads through, each with a bound on the offsets. -/
def layerGroups (first odd : ℕ) : List (V × ℕ) :=
  [(.n 7, 47), (.n 11, 22), (.n 12, 22), (.n 1310, 128), (.n (4 * odd + 1317), 113),
    (.n (4 * odd + 1323), 36), (.n (4 * odd + 2085), 25), (.n (4 * odd + 1325), 11),
    (.n (weightEnd first (4 * odd) + 34), 25), (.n (weightEnd first (4 * odd) + 278), 64)] ++
    if first = 1 then [] else [(.n (4 * odd + 2086), 11)]

/-- The calls of the body. -/
def layerCalls (first odd : ℕ) : List (Option V × String × List V × List V) :=
  [(some (.n 1315), packLoopName first odd, [.n 1316, .n 9, .n 1310, .n 1308, .n 1309], [])] ++
    if odd = 1 then [(none, "keccak_round", [.n 1318, .n 1319, .n 1320], [])] else []

theorem layerPre_kernel {first odd : ℕ} (hf : first < 2) (ho : odd < 2) :
    (layerPre first odd).all Stmt.flat = true ∧
    (layerPre first odd).filterMap Main.Stmt.addrS = [] ∧
    (layerPre first odd).filterMap Main.Stmt.allocSz =
      [(.n 1309, .inr (.n 8)), (.n 1310, .inl 128), (.n (4 * odd + 1325), .inl 11),
        (.n (weightEnd first (4 * odd) + 34), .inl 25),
        (.n (weightEnd first (4 * odd) + 278), .inl 64)] ∧
    (layerPre first odd).all (fun s ↦ !dispB s) = true ∧
    (layerPre first odd).filterMap Main.Stmt.callS = layerCalls first odd ∧
    ((layerPre first odd).filterMap Stmt.loadS).all
      (fun q ↦ (layerGroups first odd).any fun g ↦ g.1 == q.1 && decide (q.2 < g.2)) = true := by
  interval_cases first <;> interval_cases odd
  all_goals exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- Without a dispatch, a statement's frame does not depend on the valuation. -/
theorem callSF_of_not_disp (σ : Val) {s : Stmt} (h : dispB s = false) :
    s.callSF σ = Main.Stmt.callS s := by
  cases s <;> simp_all [dispB, Stmt.callSF]

theorem layerPre_callSF {first odd : ℕ} (hf : first < 2) (ho : odd < 2) (σ : Val) :
    (layerPre first odd).filterMap (Stmt.callSF σ) = layerCalls first odd := by
  obtain ⟨-, -, -, hd, hc, -⟩ := layerPre_kernel hf ho
  rw [← hc]
  refine List.filterMap_congr fun s hs ↦ callSF_of_not_disp σ ?_
  have := List.all_eq_true.mp hd s hs
  simpa using this

theorem layerPre_disp {first odd : ℕ} (hf : first < 2) (ho : odd < 2) (σ : Val) :
    ∀ s ∈ layerPre first odd, DispOk σ s := by
  obtain ⟨-, -, -, hd, -, -⟩ := layerPre_kernel hf ho
  intro s hs
  have := List.all_eq_true.mp hd s hs
  cases s <;> simp_all [dispB, DispOk]

end
end LeanVM.Guest.B1.VerifySub
