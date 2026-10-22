/-
  LeanVM.Guest.Batch.WeightsRom

  The weights' program for every child count and its certificate: doom past a count's root and
  the reads of at least one child of the bytecode's shapes, each group escaping at most `1/|E|`.
-/

module

public import LeanVM.Guest.Batch.WeightsSpec
public import LeanVM.Guest.Batch.Rom

/-!
# The weights' program in the random-oracle model

`weightsAny bytecode` reads a word naming the child count, then runs the batching of that many
children stopped at the matrices' weights (`weightsRest`), accepting when both vanish. It is
seeded as the batching (`batchSeeds`: the label's hash, then the count absorbed), so one log
carries both.

* `weightsCert`: its certificate, doom past a count's root and the reads of at least one child of
  the bytecode's shapes (`WeightsPre`), there `weightsRestSpec`'s; `weightsCert_bound`: every
  escape bound, discounted by the proof of work before its group, is at most `1/|E|`;
* `doomed_of_weightsRun`: an accepted run whose stream begins with the cells of at least one child
  of the bytecode's shapes passes a doomed boundary, for any answers `H`.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.Rom LeanVM.Node LeanVM.Guest.B1.Main
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## The program -/

/-- **The weights' program of `n` children**: their cells, then the rest. -/
noncomputable def weightsProg (bytecode : List K) (n : ℕ) : Prog Bool := do
  let cs ← readChildren (Nat.log2 bytecode.length) n
  weightsRest bytecode cs

/-- **The weights' program of every child count**: a read naming the count, then the program of
that many children. -/
noncomputable def weightsAny (bytecode : List K) : Prog Bool :=
  .read fun e ↦ weightsProg bytecode (kNat (e.limb 0))

/-- Past the children's cells, the program is `weightsRest`. -/
theorem after_weightsProg {bytecode : List K} {cs : List ChildClaims}
    (hs : ∀ c ∈ cs, ChildShaped bytecode c) (l : List Ev) :
    (weightsProg bytecode cs.length).after ((cs.flatMap childCells).map Ev.read ++ l) =
      (weightsRest bytecode cs).after l :=
  Prog.after_bind_append _ (after_readChildren hs) l

/-- After the child count's root, the program of every count is the program of that count. -/
theorem after_countRoot_weights (bytecode : List K) {n : ℕ} (hn : n < 2 ^ 64) (l : List Ev) :
    (weightsAny bytecode).after (countRoot n ++ l) = (weightsProg bytecode n).after l := by
  simp only [countRoot, List.singleton_append, weightsAny, Prog.after, limb_wordE,
    kNat_ofBits hn]

/-- The node of `weightsAny` at a child count's root is the program of that count. -/
theorem nodeAt_countRoot_weights (bytecode : List K) {n : ℕ} (hn : n < 2 ^ 64) :
    nodeAt (weightsAny bytecode) (countRoot n) = weightsProg bytecode n := by
  rw [nodeAt, ← List.append_nil (countRoot n), after_countRoot_weights bytecode hn]
  simp [Prog.after]

/-- A child count's root is a root of `weightsAny`. -/
theorem rootOk_countRoot_weights (bytecode : List K) {n : ℕ} (hn : n < 2 ^ 64) :
    RootOk (weightsAny bytecode) (countRoot n) := by
  have ha : (weightsAny bytecode).after (countRoot n) = some (weightsProg bytecode n) := by
    rw [← List.append_nil (countRoot n)]
    exact (after_countRoot_weights bytecode hn []).trans (by simp [Prog.after])
  exact ⟨reachable_of_after_reads [wordE (K.ofBits n)] ha,
    boundary_map_read (l := [wordE (K.ofBits n)]) (by simp),
    grindBits_map_read [wordE (K.ofBits n)], commits_map_read [wordE (K.ofBits n)],
    by rw [ha]; rfl⟩

/-- The program after the children makes no proof of work. -/
theorem movesOK_weightsRest (bytecode : List K) (cs : List ChildClaims) :
    MovesOK (· ≤ 64) False (weightsRest bytecode cs) := by
  unfold weightsRest
  generalize 2 * blake2sR1csLogSize = m
  refine MovesOK.seq (movesOK_sampleLB _) fun _ ↦ ?_
  refine MovesOK.seq (movesOK_roundsProg _ _) fun _ ↦ ?_
  refine MovesOK.seq (movesOK_sampleLM _) fun _ ↦ ?_
  refine MovesOK.seq (movesOK_roundsProg _ _) fun _ ↦ ?_
  exact MovesOK.seq (movesOK_require _ _) fun _ ↦ trivial

/-! ## The certificate -/

/-- **A doomed prefix of the weights' program**: fewer than `2^64` children of the bytecode's
shapes, at least one. -/
structure WeightsPre (bytecode : List K) where
  /-- The children. -/
  cs : List ChildClaims
  /-- Their count is a word. -/
  lt : cs.length < 2 ^ 64
  /-- They have the bytecode's shapes. -/
  shaped : ∀ c ∈ cs, ChildShaped bytecode c
  /-- There is at least one. -/
  ne : cs ≠ []

namespace WeightsPre

variable {bytecode : List K}

/-- The history of a prefix: the child count's root, then the children's cells read. -/
def hist (p : WeightsPre bytecode) : List Ev :=
  countRoot p.cs.length ++ (p.cs.flatMap childCells).map Ev.read

/-- The certificate after a prefix's children: `weightsRestSpec`'s. -/
noncomputable def cert (p : WeightsPre bytecode) : Cert (weightsRest bytecode p.cs) :=
  (weightsRestSpec p.shaped p.ne).toCertOfLead

/-- A prefix's history is the reads of the count's word and the children's cells. -/
theorem hist_eq (p : WeightsPre bytecode) :
    p.hist = (wordE (K.ofBits p.cs.length) :: p.cs.flatMap childCells).map Ev.read := rfl

/-- Past a prefix's history, the program is `weightsRest` of its children. -/
theorem after_hist (p : WeightsPre bytecode) :
    (weightsAny bytecode).after p.hist = some (weightsRest bytecode p.cs) := by
  rw [hist, after_countRoot_weights bytecode p.lt, ← List.append_nil (List.map _ _),
    after_weightsProg p.shaped]
  simp [Prog.after]

/-- A prefix's history commits nothing. -/
theorem commits_hist (p : WeightsPre bytecode) : commits p.hist = [] := by
  rw [hist_eq]; exact commits_map_read _

/-- A prefix's history adds no proof of work. -/
theorem grindBits_hist (p : WeightsPre bytecode) (h' : List Ev) :
    grindBits (p.hist ++ h') = grindBits h' := by
  rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
  · rw [List.append_nil, hist_eq]; exact grindBits_map_read _
  · rw [List.concat_eq_append, ← List.append_assoc]
    simp [grindBits]

/-- **Prefixes are prefix-free**: two prefixes on one history are one prefix. -/
theorem hist_inj {p q : WeightsPre bytecode} {h' h'' : List Ev}
    (he : p.hist ++ h' = q.hist ++ h'') : p = q ∧ h' = h'' := by
  simp only [hist, countRoot, List.cons_append, List.nil_append, List.cons.injEq,
    Ev.read.injEq] at he
  obtain ⟨h0, he⟩ := he
  have hl : p.cs.length = q.cs.length := ofBits_injective p.lt q.lt (wordE_injective h0)
  obtain ⟨e1, e2⟩ := List.append_inj he (by
    simp only [List.length_map, length_flatMap_childCells p.shaped,
      length_flatMap_childCells q.shaped, hl])
  have hcs := eq_of_flatMap_childCells p.shaped q.shaped
    (List.map_injective_iff.mpr (fun a b h ↦ Ev.read.inj h) e1)
  refine ⟨?_, e2⟩
  cases p
  cases q
  subst hcs
  rfl

end WeightsPre

/-- **Doom of the weights' program**: past a prefix, the doom of its certificate on the rest. -/
def weightsD (bytecode : List K) (h : List Ev) : Prop :=
  ∃ (p : WeightsPre bytecode) (h' : List Ev), h = p.hist ++ h' ∧ p.cert.D h'

open Classical in
/-- The escape bound of the weights' program: its certificate's past a prefix, `0` elsewhere. -/
noncomputable def weightsCertε (bytecode : List K) (h : List Ev) : ℝ≥0∞ :=
  if hx : ∃ (p : WeightsPre bytecode) (h' : List Ev), h = p.hist ++ h' then
    hx.choose.cert.ε hx.choose_spec.choose
  else 0

section Cert

variable {bytecode : List K}

/-- Past a prefix, doom is the prefix certificate's. -/
theorem weightsD_iff (p : WeightsPre bytecode) (h' : List Ev) :
    weightsD bytecode (p.hist ++ h') ↔ p.cert.D h' := by
  constructor
  · rintro ⟨q, h'', he, hD⟩
    obtain ⟨rfl, rfl⟩ := WeightsPre.hist_inj he
    exact hD
  · intro hD
    exact ⟨p, h', rfl, hD⟩

/-- Past a prefix, the escape bound is the prefix certificate's. -/
theorem weightsCertε_eq (p : WeightsPre bytecode) (h' : List Ev) :
    weightsCertε bytecode (p.hist ++ h') = p.cert.ε h' := by
  have key : ∀ (q : WeightsPre bytecode) (h'' : List Ev), p.hist ++ h' = q.hist ++ h'' →
      q.cert.ε h'' = p.cert.ε h' := by
    intro q h'' he
    obtain ⟨rfl, rfl⟩ := WeightsPre.hist_inj he
    rfl
  unfold weightsCertε
  split
  · rename_i hx
    exact key _ _ hx.choose_spec.choose_spec
  · rename_i hx
    exact absurd ⟨p, h', rfl⟩ hx

end Cert

/-- **The certificate of the weights' program**, for every child count. -/
noncomputable def weightsCert (bytecode : List K) : Cert (weightsAny bytecode) where
  D := weightsD bytecode
  ε := weightsCertε bytecode
  read := by
    intro h k e hr ha hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    rw [List.append_assoc, weightsD_iff]
    exact p.cert.read e (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hDp
  grind := by
    intro h b k hr ha hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    rw [List.append_assoc, weightsD_iff]
    exact p.cert.grind (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hDp
  commit := by
    intro h ht w k word hr ha hw hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    rw [List.append_assoc, weightsD_iff]
    exact p.cert.commit word (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hw hDp
  group := by
    intro h q hr hbd ha hq hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    rw [esc_drop (h₀ := p.hist) p.commits_hist (weightsD_iff p), weightsCertε_eq]
    exact p.cert.group (reachable_drop hap p.commits_hist hr h' rfl)
      (boundary_drop hbd) (by rwa [after_drop hap] at ha) hq hDp
  final := by
    intro h hr ha hD
    obtain ⟨p, h', rfl, hDp⟩ := hD
    have hap := p.after_hist
    exact p.cert.final (reachable_drop hap p.commits_hist hr h' rfl)
      (by rwa [after_drop hap] at ha) hDp

/-- **The certificate's bound**: every escape bound, discounted by the proof of work before its
group, is at most `1/|E|`. -/
theorem weightsCert_bound (bytecode : List K) (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (weightsCert bytecode).ε h ≤ invE := by
  by_cases hx : ∃ (p : WeightsPre bytecode) (h' : List Ev), h = p.hist ++ h'
  · obtain ⟨p, h', rfl⟩ := hx
    show _ * weightsCertε bytecode _ ≤ _
    rw [weightsCertε_eq, p.grindBits_hist]
    by_cases hr : (weightsRest bytecode p.cs).Reachable h'
    · rw [min_eq_left ((movesOK_weightsRest bytecode p.cs).grindBits_le hr)]
      exact Spec.toCertOfLead_bound _ le_rfl h'
    · simp only [WeightsPre.cert, Spec.toCertOfLead, Spec.toCert_ε, hr, false_and,
        ↓reduceIte, mul_zero, zero_le]
  · show _ * weightsCertε bytecode _ ≤ _
    simp only [weightsCertε, hx, ↓reduceDIte, mul_zero, zero_le]

/-! ## Doom on accepted runs -/

/-- **At least one child dooms an accepted run**, for any answers `H`: past the count's root and
the children's reads, `weightsRestSpec` is doomed at its start. -/
theorem doomed_of_weightsRun {bytecode : List K} {M : ℕ} (hM : M ≤ 2 ^ 64 - 1)
    {H : Bytes → Option Digest} {x : Fin M} {π : Proof}
    (hv : Rom.verify H ((batchSeeds M hM).seed x)
      (nodeAt (weightsAny bytecode) ((batchSeeds M hM).root x)) π = some true)
    (hc : ∃ cs : List ChildClaims, cs.length = x ∧ (∀ c ∈ cs, ChildShaped bytecode c) ∧
      cs ≠ [] ∧ cs.flatMap childCells <+: π.stream) :
    ∃ h₀, h₀ <+: extractedFrom H ((batchSeeds M hM).seed x)
        (nodeAt (weightsAny bytecode) ((batchSeeds M hM).root x)) ((batchSeeds M hM).root x) π ∧
      ((batchSeeds M hM).root x).length ≤ h₀.length ∧ Boundary h₀ ∧
        (weightsCert bytecode).D h₀ := by
  obtain ⟨cs, hlen, hs, hne, hpre⟩ := hc
  have hx := x.2
  have hz : (x : ℕ) < 2 ^ 64 := by omega
  have hlt : cs.length < 2 ^ 64 := by rw [hlen]; exact hz
  let p : WeightsPre bytecode := ⟨cs, hlt, hs, hne⟩
  have hroot : (batchSeeds M hM).root x = countRoot x := rfl
  rw [hroot, nodeAt_countRoot_weights bytecode hz] at hv
  refine ⟨p.hist, ?_, ?_, ?_, ?_⟩
  · rw [hroot, nodeAt_countRoot_weights bytecode hz, extractedFrom_eq _ _ _ _ _ hv]
    show countRoot cs.length ++ _ <+: _
    rw [hlen]
    refine (List.prefix_append_right_inj _).mpr ?_
    obtain ⟨seed, s, -, hxr⟩ := xrun_of_verify hv
    have ha : (weightsProg bytecode x).after ((cs.flatMap childCells).map Ev.read) =
        some (weightsRest bytecode cs) := by
      rw [← hlen, ← List.append_nil (List.map _ _), after_weightsProg hs]
      simp [Prog.after]
    simpa using xrun_reads _ _ _ _ [] ha hpre hxr
  · rw [hroot]
    simp [WeightsPre.hist, countRoot, p]
  · rw [p.hist_eq]
    exact boundary_map_read (by simp)
  · exact ⟨p, [], by rw [List.append_nil], (weightsRestSpec p.shaped p.ne).start_D [] rfl⟩

end
end LeanVM.Guest.Batch
