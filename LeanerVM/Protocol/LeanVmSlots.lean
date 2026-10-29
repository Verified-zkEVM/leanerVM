/-
  LeanerVM.Protocol.LeanVmSlots

  The challenges of leanVM's compiled protocol read off squeezes: one squeeze for an element of
  `E`, five for the fingerprint challenges, and as many as WHIR's query positions need; each uniform
  when its squeezes are, and read so by the decoder of the chain's history.
-/

module

public import LeanerVM.Protocol.ReaderSlots
public import LeanerVM.Protocol.DecodeChain
public import LeanerVM.Protocol.Verify.Count

/-!
# leanVM's challenges, read off squeezes

Three kinds of challenge occur in the compiled protocol of leanVM, each a `UniformSlot`:

* an element of `E` (`eSlot`): one squeeze, the challenge of its digest (`FsState.challengeOf`);
* the fingerprint challenges `(α, β)` (`fingerprintUSlot`): five squeezes, `α` the first four's
  challenges, `β` the fifth's;
* WHIR's `t` query positions of `b` bits (`positionsUSlot`): the squeezes `walkPositions` takes,
  `⌊192/b⌋` positions to a squeeze, low bits first; uniform by `prEvent_positions_uniform`, as the
  positions are `challengePositions` (`positionsOf_posChunks`).

The history reader's slots read them (`readsSqueezes_sample`, `readsSqueezes_fingerprintSlot`,
`readsSqueezes_positionsSlot`), and every slot of the history reader is blind to the states of
observes and nonces (`blind_*`).

The families follow the compiled protocol's decoder phase by phase: the front (`frontFam`, the
commitment, the bus phase, the table sumcheck, the public input, the Flock phase and the opening's
`λ`), then WHIR's levels (`levelFam`, `finalFam`, `ladderFam`), whose nonce steps are flagged
(`levelFlags`, `finalFlags`). `readsWell_compiledDec`: the decoder of the compiled protocol reads
well by `compiledFam` and `compiledFlags` when every level's positions fit a squeeze (`posOk`),
and every challenge reads a squeeze at least (`pos_compiledFam`).
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters LeanerVM.Semantics Blake2sHash OracleComp OracleSpec ProtocolSpec
open StepSchedule Verify DecodeChain

@[expose] public section

namespace LeanVmSlots

/-! ## One squeeze -/

/-- The challenge of `m` squeezes' digests, in order. -/
abbrev chals {m : ℕ} (ds : Fin m → Digest) : List E := List.ofFn fun i ↦ FsState.challengeOf (ds i)

/-- **An element of `E`**: one squeeze, the challenge of its digest. -/
def eSlot : UniformSlot E where
  inst := inferInstance
  slot :=
    { m := 1
      assemble := fun ds ↦ FsState.challengeOf (ds 0)
      uniform := fun p ↦ (prEvent_challengeOf_tuple 1 fun x ↦ p (x 0)).trans
        (SampleableType.prEvent_uniformSample_equiv (Equiv.funUnique (Fin 1) E) p) }

private theorem readsSqueezes_sample : ReadsSqueezes historyOps.sample eSlot := by
  show ∀ (ds : Fin 1 → Digest) rest, (Slot.next challengeOf).read
    (squeezeBlocks (List.ofFn ds) ++ rest) = some (FsState.challengeOf (ds 0), rest)
  intro ds rest
  rw [List.ofFn_succ, List.ofFn_zero]
  rfl

/-- `k` squeezes read as their challenges. -/
private theorem read_samples : ∀ (ds : List Digest) (rest : List (Block × Digest)),
    (samples historyOps ds.length).read (squeezeBlocks ds ++ rest) =
      some (ds.map FsState.challengeOf, rest)
  | [], _ => rfl
  | d :: ds, rest => by
    simp only [List.length_cons, samples, Slot.read_bind, squeezeBlocks, List.map_cons,
      List.cons_append]
    show ((Slot.next challengeOf).read ((Block.squeeze, d) :: _)).bind _ = _
    rw [Slot.read_next_cons]
    simp only [challengeOf, Option.map_some, Option.bind_some]
    have h := read_samples ds rest
    simp only [squeezeBlocks] at h
    rw [h]
    rfl

/-! ## The fingerprint challenges -/

/-- Five elements as four and one. -/
def fiveEquiv : (Fin 5 → E) ≃ (Fin 4 → E) × E where
  toFun x := (fun i ↦ x i.castSucc, x (Fin.last 4))
  invFun p := Fin.snoc p.1 p.2
  left_inv x := Fin.snoc_init_self x
  right_inv p := Prod.ext (funext fun i ↦ Fin.snoc_castSucc (α := fun _ ↦ E) p.2 p.1 i)
    (Fin.snoc_last (α := fun _ ↦ E) p.2 p.1)

/-- **The fingerprint challenges**: five squeezes, the first four's challenges, then the
fifth's. -/
def fingerprintUSlot : UniformSlot ((Fin 4 → E) × E) where
  inst := inferInstance
  slot :=
    { m := 5
      assemble := fun ds ↦ fiveEquiv fun i ↦ FsState.challengeOf (ds i)
      uniform := fun p ↦ (prEvent_challengeOf_tuple 5 fun x ↦ p (fiveEquiv x)).trans
        (SampleableType.prEvent_uniformSample_equiv fiveEquiv p) }

private theorem readsSqueezes_fingerprintSlot : ReadsSqueezes fingerprintSlot fingerprintUSlot := by
    show ∀ (ds : Fin 5 → Digest) rest, fingerprintSlot.read (squeezeBlocks (List.ofFn ds) ++ rest) =
      some (fingerprintUSlot.assemble ds, rest)
    intro ds rest
    have hsplit : squeezeBlocks (List.ofFn ds) ++ rest =
        squeezeBlocks (List.ofFn fun i : Fin 4 ↦ ds i.castSucc) ++
          ((Block.squeeze, ds (Fin.last 4)) :: rest) := by
      simp [squeezeBlocks, List.ofFn_succ]
    rw [hsplit]
    unfold fingerprintSlot
    rw [Slot.read_bind]
    have h4 := read_samples (List.ofFn fun i : Fin 4 ↦ ds i.castSucc)
      ((Block.squeeze, ds (Fin.last 4)) :: rest)
    rw [List.length_ofFn] at h4
    rw [h4, Option.bind_some, Slot.read_bind]
    show ((Slot.next challengeOf).read ((Block.squeeze, ds (Fin.last 4)) :: rest)).bind _ = _
    rw [Slot.read_next_cons]
    simp only [challengeOf, Option.map_some, Option.bind_some, Slot.read_pure]
    congr 2
    refine Prod.ext (funext fun i ↦ ?_) rfl
    simp only [List.getD_eq_getElem?_getD, List.map_ofFn, List.getElem?_ofFn]
    fin_cases i <;> rfl

/-! ## WHIR's query positions -/

/-- The squeezes `walkPositions depth fuel need` takes. -/
def posSqueezes (depth : ℕ) : (fuel need : ℕ) → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, need + 1 => 1 + posSqueezes depth fuel (need + 1 - min (192 / depth) (need + 1))

/-- The positions `walkPositions depth fuel need` gives from the challenges `xs` of its squeezes. -/
def posChunks (depth : ℕ) : (fuel need : ℕ) → List E → List ℕ
  | 0, _, _ => []
  | _ + 1, 0, _ => []
  | fuel + 1, need + 1, xs =>
    (List.range (min (192 / depth) (need + 1))).map
        (fun c ↦ chalBits (xs.headD 0) / 2 ^ (c * depth) % 2 ^ depth) ++
      posChunks depth fuel (need + 1 - min (192 / depth) (need + 1)) xs.tail

/-- The walk's positions, read off its squeezes. -/
private theorem read_walkPositions (depth : ℕ) : ∀ (fuel need : ℕ) (ds : List Digest)
    (rest : List (Block × Digest)), ds.length = posSqueezes depth fuel need →
    (walkPositions historyOps depth fuel need).read (squeezeBlocks ds ++ rest) =
      some (posChunks depth fuel need (ds.map FsState.challengeOf), rest)
  | 0, _, ds, rest, h => by
    rw [List.eq_nil_of_length_eq_zero h]
    rfl
  | _ + 1, 0, ds, rest, h => by
    rw [List.eq_nil_of_length_eq_zero h]
    rfl
  | fuel + 1, need + 1, ds, rest, h => by
    rcases ds with _ | ⟨d, ds⟩
    · simp only [List.length_nil, posSqueezes] at h
      omega
    simp only [List.length_cons, posSqueezes] at h
    have ih := read_walkPositions depth fuel (need + 1 - min (192 / depth) (need + 1)) ds rest
      (by omega)
    simp only [walkPositions, Slot.read_bind, squeezeBlocks, List.map_cons, List.cons_append]
    show ((Slot.next challengeOf).read ((Block.squeeze, d) :: _)).bind _ = _
    rw [Slot.read_next_cons]
    simp only [challengeOf, Option.map_some, Option.bind_some]
    simp only [squeezeBlocks] at ih
    rw [ih]
    rfl

/-- The challenges of a schedule's position chunks: chunk `q % K` of challenge `q / K`, `K` the
positions a squeeze gives. -/
private theorem getD_posChunks {depth : ℕ} (hK : 0 < 192 / depth) : ∀ (fuel need : ℕ) (xs : List E),
    need ≤ fuel → ∀ q < need, (posChunks depth fuel need xs).getD q 0 =
      chalBits (xs.getD (q / (192 / depth)) 0) / 2 ^ (q % (192 / depth) * depth) % 2 ^ depth
  | 0, _, _, hn, q, hq => absurd hq (by omega)
  | _ + 1, 0, _, _, q, hq => absurd hq (by omega)
  | fuel + 1, need + 1, xs, hn, q, hq => by
    simp only [posChunks]
    set K := 192 / depth with hKdef
    by_cases hqc : q < min K (need + 1)
    · rw [List.getD_append _ _ _ _ (by simpa using hqc)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hqc,
        Option.map_some, Option.getD_some]
      have hqK : q < K := lt_of_lt_of_le hqc (min_le_left _ _)
      rw [Nat.div_eq_of_lt hqK, Nat.mod_eq_of_lt hqK]
      rcases xs with _ | ⟨x, xs⟩ <;> rfl
    · have hc : min K (need + 1) = K := by omega
      rw [List.getD_append_right _ _ _ _ (by simp; omega), List.length_map, List.length_range,
        hc, getD_posChunks hK fuel (need + 1 - K) xs.tail (by omega) (q - K) (by omega),
        ← Nat.mod_eq_sub_mod (by omega)]
      have hdiv : q / K = (q - K) / K + 1 := Nat.div_eq_sub_div hK (by omega)
      rw [hdiv]
      rcases xs with _ | ⟨x, xs⟩ <;> simp [hKdef]

/-- Enough squeezes for the positions: `⌊192/depth⌋` to a squeeze. -/
private theorem le_posSqueezes_mul {depth : ℕ} (hK : 0 < 192 / depth) : ∀ fuel need, need ≤ fuel →
    need ≤ posSqueezes depth fuel need * (192 / depth)
  | 0, _, hn => by simp [posSqueezes]; omega
  | _ + 1, 0, _ => Nat.zero_le _
  | fuel + 1, need + 1, hn => by
    have ih := le_posSqueezes_mul hK fuel (need + 1 - min (192 / depth) (need + 1)) (by omega)
    simp only [posSqueezes, Nat.add_mul, one_mul]
    omega

/-- The walk's positions are `challengePositions` of its squeezes' challenges. -/
theorem positionsOf_posChunks {b t : ℕ} (hK : 0 < 192 / b) (xs : List E) :
    positionsOf t b (posChunks b t t xs) = challengePositions b t xs := by
  funext q
  apply Fin.ext
  simp only [positionsOf, challengePositions, getD_posChunks hK t t xs le_rfl q q.2, Nat.mod_mod]
  rfl

/-- **WHIR's `t` query positions of `b` bits**: the squeezes the walk takes, uniform since they
are `challengePositions` of enough squeezes. -/
def positionsUSlot (b t : ℕ) (hK : 0 < 192 / b) : UniformSlot (Fin t → Fin (2 ^ b)) where
  inst := inferInstance
  slot :=
    { m := posSqueezes b t t
      assemble := fun ds ↦ positionsOf t b (posChunks b t t (chals ds))
      uniform := fun p ↦ by
        simp only [positionsOf_posChunks hK]
        exact prEvent_positions_uniform (le_posSqueezes_mul hK t t le_rfl) p }

private theorem readsSqueezes_positionsSlot (b t : ℕ) (hK : 0 < 192 / b) :
    ReadsSqueezes (positionsSlot b t) (positionsUSlot b t hK) := fun ds rest ↦ by
  rw [positionsSlot, Slot.read_mapM,
    read_walkPositions b t t (List.ofFn ds) rest (List.length_ofFn), Option.map_some, List.map_ofFn]
  rfl

/-! ## The history reader's slots are blind -/

/-- Blindness, as a property of slots that `bind` keeps; its count is ignored. -/
private def blindGrade : MonadGrade (Slot Reading) where
  P a _ := a.Blind
  pure x := Slot.Blind.pure x
  bind ha hf := Slot.Blind.bind ha hf

private theorem historyOps_blind (c : StepCounts) : ChainOps.Graded blindGrade historyOps c where
  nextScalar := Slot.Blind.next fun ⟨b, d⟩ ↦ by cases b <;> rfl
  sample := Slot.Blind.next fun ⟨b, d⟩ ↦ by cases b <;> rfl
  nextRoot := by
    refine blindGrade.bind (n := c.scalar) (Slot.Blind.next fun ⟨b, d⟩ ↦ by cases b <;> rfl)
      fun a ↦ blindGrade.bind (n := c.scalar) (k := c.root)
        (Slot.Blind.next fun ⟨b, d⟩ ↦ by cases b <;> rfl) fun b ↦ ?_
    show Slot.Blind _
    split
    · exact Slot.Blind.pure _
    · exact Slot.Blind.fail
  checkPow _ := Slot.Blind.next fun ⟨b, d⟩ ↦ by cases b <;> rfl

private theorem blind_nextScalars (k : ℕ) : (historyOps.nextScalars k).Blind :=
  nextScalars_grade (historyOps_blind ⟨0, 0, 0, fun _ ↦ 0⟩) k

private theorem blind_samples (k : ℕ) : (samples historyOps k).Blind :=
  samples_grade (historyOps_blind ⟨0, 0, 0, fun _ ↦ 0⟩) k

private theorem blind_sample : historyOps.sample.Blind :=
  (historyOps_blind ⟨0, 0, 0, fun _ ↦ 0⟩).sample

private theorem blind_nextScalar : historyOps.nextScalar.Blind :=
  (historyOps_blind ⟨0, 0, 0, fun _ ↦ 0⟩).nextScalar

private theorem blind_checkPow (bits : ℕ) : (historyOps.checkPow bits).Blind :=
  (historyOps_blind ⟨0, 0, 0, fun _ ↦ 0⟩).checkPow bits

private theorem blind_vecSlot (n : ℕ) : (vecSlot n).Blind := (blind_nextScalars n).mapM _

private theorem blind_polySlot (d : ℕ) (claim : Thunk E) (eq? : Thunk (Option E)) :
    (polySlot d claim eq?).Blind := by
  refine Slot.Blind.bind (blind_nextScalars d) fun w ↦ ?_
  split
  · exact Slot.Blind.pure _
  · exact Slot.Blind.fail

private theorem blind_positionsSlot (b t : ℕ) : (positionsSlot b t).Blind :=
  (walkPositions_grade (historyOps_blind ⟨0, 0, 0, fun _ ↦ 0⟩) b t t).mapM _

private theorem blind_fingerprintSlot : fingerprintSlot.Blind :=
  Slot.Blind.bind (blind_samples 4) fun _ ↦ Slot.Blind.bind blind_sample fun _ ↦
    Slot.Blind.pure _

private theorem blind_rootsSlot : rootsSlot.Blind :=
  Slot.Blind.bind blind_nextScalar fun _ ↦ Slot.Blind.bind blind_nextScalar fun _ ↦
    Slot.Blind.pure _

private theorem blind_childrenSlot (ρ : ℕ) : (childrenSlot ρ).Blind :=
  Slot.Blind.bind (blind_vecSlot _) fun _ ↦ Slot.Blind.bind (blind_vecSlot _) fun _ ↦
    Slot.Blind.bind (blind_vecSlot _) fun _ ↦ Slot.Blind.pure _

private theorem blind_commitSlot {M : Type} (ann : List E) (w : M) : (commitSlot ann w).Blind := by
  refine Slot.Blind.bind (blind_nextScalars 8) fun xs ↦ ?_
  split
  · exact ((historyOps_blind ⟨0, 0, 0, fun _ ↦ 0⟩).nextRoot).mapM _
  · exact Slot.Blind.fail

/-! ## The front phases -/

section Front

open ChalSlots SlotDecoder

private theorem eSlot_pos : 0 < eSlot.m := Nat.one_pos

private theorem readsWell_roundsDec (d : ℕ) (eq? : ℕ → Option E) (σ : Thunk E × ℕ) (m : ℕ) :
    (roundsDec d eq? σ m).ReadsWell (ChalSlots.rounds eSlot d m) fun _ ↦ false :=
  .of_squeezes (squeezeReads_rounds (fun _ ↦ readsSqueezes_sample) σ m)
    (blind_rounds (fun _ ↦ blind_polySlot _ _ _) (fun _ ↦ blind_sample) σ m)

private theorem readsWell_samples (k : ℕ) :
    (SlotDecoder.draws historyOps.sample k).ReadsWell (ChalSlots.draws eSlot k) fun _ ↦ false :=
  .of_squeezes (squeezeReads_draws readsSqueezes_sample k) (blind_draws blind_sample k)

private theorem readsWell_sample :
    (single (pSpec := Protocol.draw E) historyOps.sample).ReadsWell (ChalSlots.draw eSlot)
      fun _ ↦ false :=
  readsWell_draw readsSqueezes_sample blind_sample

/-- The challenges of a layer of the grand product. -/
def stepFam (ρ m : ℕ) : ChalSlots (stepSpec E 3 ρ m) :=
  ChalSlots.append (ChalSlots.append (ChalSlots.append (ChalSlots.draw eSlot)
    (ChalSlots.rounds eSlot (2 ^ ρ) m)) (ChalSlots.say _)) (ChalSlots.draws eSlot ρ)

private theorem pos_stepFam (ρ m : ℕ) : (stepFam ρ m).Pos :=
  pos_append (pos_append (pos_append (pos_draw eSlot_pos) (pos_rounds eSlot_pos _ _))
    (pos_say _)) (pos_draws eSlot_pos _)

private theorem readsWell_layerDec (st : GkrState) (ρ m : ℕ) :
    (layerDec st ρ m).ReadsWell (stepFam ρ m) fun _ ↦ false :=
  readsWell_append_none (readsWell_append_none (readsWell_append_none readsWell_sample
    fun _ ↦ readsWell_roundsDec _ _ _ _) fun _ ↦ readsWell_say (blind_childrenSlot ρ))
    fun _ ↦ readsWell_samples ρ

/-- The challenges of `k` layers of radix four. -/
def stepsFam : (k m : ℕ) → ChalSlots (stepsSpec E 3 k m)
  | 0, _ => ChalSlots.empty
  | k + 1, m => ChalSlots.append (stepFam 2 m) (stepsFam k (m + 2))

private theorem pos_stepsFam : ∀ k m, (stepsFam k m).Pos
  | 0, _ => pos_empty
  | k + 1, m => pos_append (pos_stepFam 2 m) (pos_stepsFam k (m + 2))

private theorem readsWell_stepsDec : ∀ (st : GkrState) (k m : ℕ),
    (stepsDec st k m).ReadsWell (stepsFam k m) fun _ ↦ false
  | _, 0, _ => readsWell_empty
  | st, k + 1, m => readsWell_append_none (readsWell_layerDec st 2 m)
      fun t ↦ readsWell_stepsDec (layerNext t) k (m + 2)

/-- The challenges of the binary layer, if there is one. -/
def oddFam : (r : ℕ) → ChalSlots (oddSpec E 3 r)
  | 0 => ChalSlots.empty
  | _ + 1 => stepFam 1 0

private theorem pos_oddFam : ∀ r, (oddFam r).Pos
  | 0 => pos_empty
  | _ + 1 => pos_stepFam 1 0

private theorem readsWell_oddDec (st : GkrState) :
    ∀ r, (oddDec st r).ReadsWell (oddFam r) fun _ ↦ false
  | 0 => readsWell_empty
  | _ + 1 => readsWell_layerDec st 1 0

/-- The challenges of the grand product. -/
def gkrFam (μ : ℕ) : ChalSlots (gkrSpec E 3 μ) :=
  ChalSlots.append (ChalSlots.append (oddFam (μ % 2)) (stepsFam (μ / 2) (μ % 2)))
    (ChalSlots.draw eSlot)

private theorem pos_gkrFam (μ : ℕ) : (gkrFam μ).Pos :=
  pos_append (pos_append (pos_oddFam _) (pos_stepsFam _ _)) (pos_draw eSlot_pos)

private theorem readsWell_gkrDec (st : GkrState) (μ : ℕ) :
    (gkrDec st μ).ReadsWell (gkrFam μ) fun _ ↦ false :=
  readsWell_append_none (readsWell_append_none (readsWell_oddDec st _)
    fun _ ↦ readsWell_stepsDec _ _ _) fun _ ↦ readsWell_sample

variable (I : M3Instance)

/-- The challenges of the bus phase. -/
def busFam : ChalSlots (busSpec I) :=
  ChalSlots.append (ChalSlots.append (ChalSlots.append (ChalSlots.draw fingerprintUSlot)
    (ChalSlots.say _)) (gkrFam I.μBus)) (ChalSlots.say _)

private theorem pos_busFam : (busFam I).Pos :=
  pos_append (pos_append (pos_append (pos_draw (Nat.succ_pos 4)) (pos_say _)) (pos_gkrFam _))
    (pos_say _)

private theorem readsWell_busDec : (busDec I).ReadsWell (busFam I) fun _ ↦ false :=
  readsWell_append_none (readsWell_append_none (readsWell_append_none
    (readsWell_draw readsSqueezes_fingerprintSlot blind_fingerprintSlot)
    fun _ ↦ readsWell_say blind_rootsSlot) fun _ ↦ readsWell_gkrDec _ _)
    fun _ ↦ readsWell_say (blind_vecSlot _)

/-- The challenges of the table sumcheck. -/
def tableFam : ChalSlots (tableSpec I) :=
  ChalSlots.append (ChalSlots.append (ChalSlots.draw eSlot) (ChalSlots.rounds eSlot 3 I.τmax))
    (ChalSlots.say _)

private theorem pos_tableFam : (tableFam I).Pos :=
  pos_append (pos_append (pos_draw eSlot_pos) (pos_rounds eSlot_pos _ _)) (pos_say _)

private theorem readsWell_tableDec (s : Thunk (I.Stmt × BusOut I)) :
    (tableDec I s).ReadsWell (tableFam I) fun _ ↦ false :=
  readsWell_append_none (readsWell_append_none readsWell_sample
    fun _ ↦ readsWell_roundsDec _ _ _ _) fun _ ↦ readsWell_say (blind_vecSlot _)

/-- The challenge of the public input. -/
def pubFam : ChalSlots pubSpec
  | ⟨0, _⟩, _ => eSlot
  | ⟨1, _⟩, h => nomatch h

private theorem pos_pubFam : pubFam.Pos
  | ⟨0, _⟩, _ => eSlot_pos
  | ⟨1, _⟩, h => nomatch h

private theorem readsWell_pubDec (n : ℕ) : (pubDec n).ReadsWell pubFam fun _ ↦ false :=
  .of_squeezes (fun | ⟨0, _⟩, _, _ => readsSqueezes_sample | ⟨1, _⟩, h, _ => nomatch h)
    fun | ⟨0, _⟩, _ => blind_sample | ⟨1, _⟩, _ => blind_nextScalars n

/-- The challenges of the Flock phase for `2 ^ k` compressions. -/
def flockFamOf (k : ℕ) : ChalSlots (flockSpecOf k) :=
  ChalSlots.append (ChalSlots.append (ChalSlots.append (ChalSlots.append (ChalSlots.append
    (ChalSlots.append (ChalSlots.append (ChalSlots.append (ChalSlots.append
    (ChalSlots.draws eSlot (k + 1)) (ChalSlots.say _)) (ChalSlots.draw eSlot))
    (ChalSlots.rounds eSlot 2 8)) (ChalSlots.rounds eSlot 2 k)) (ChalSlots.say _))
    (ChalSlots.draw eSlot)) (ChalSlots.rounds eSlot 2 8)) (ChalSlots.say _))
    (ChalSlots.draws eSlot 6)

private theorem pos_flockFamOf (k : ℕ) : (flockFamOf k).Pos :=
  pos_append (pos_append (pos_append (pos_append (pos_append (pos_append (pos_append
    (pos_append (pos_append (pos_draws eSlot_pos _) (pos_say _)) (pos_draw eSlot_pos))
    (pos_rounds eSlot_pos _ _)) (pos_rounds eSlot_pos _ _)) (pos_say _)) (pos_draw eSlot_pos))
    (pos_rounds eSlot_pos _ _)) (pos_say _)) (pos_draws eSlot_pos _)

private theorem readsWell_flockDecOf (k : ℕ) :
    (flockDecOf k).ReadsWell (flockFamOf k) fun _ ↦ false := by
  unfold flockDecOf flockFamOf
  exact readsWell_append_none (readsWell_append_none (readsWell_append_none (readsWell_append_none
    (readsWell_append_none (readsWell_append_none (readsWell_append_none (readsWell_append_none
    (readsWell_append_none (readsWell_samples _) fun _ ↦ readsWell_say (blind_vecSlot _))
    fun _ ↦ readsWell_sample) fun _ ↦ readsWell_roundsDec _ _ _ _)
    fun _ ↦ readsWell_roundsDec _ _ _ _) fun _ ↦ readsWell_say (blind_vecSlot _))
    fun _ ↦ readsWell_sample) fun _ ↦ readsWell_roundsDec _ _ _ _)
    fun _ ↦ readsWell_say (blind_vecSlot _)) fun _ ↦ readsWell_samples _

/-- The challenges of the Flock slot. -/
def flockFam : (o : Option (FlockRegion I.toShape)) → ChalSlots (flockSpecOpt I o)
  | none => ChalSlots.empty
  | some r => flockFamOf r.kBatch

private theorem pos_flockFam : ∀ o, (flockFam I o).Pos
  | none => pos_empty
  | some r => pos_flockFamOf r.kBatch

private theorem readsWell_flockDec : ∀ o, (flockDec I o).ReadsWell (flockFam I o) fun _ ↦ false
  | none => readsWell_empty
  | some r => readsWell_flockDecOf r.kBatch

end Front

/-! ## The compiled protocol -/

section Compiled

open ChalSlots SlotDecoder Whir

/-- A nonce step's slot reads exactly the nonce step. -/
private theorem readsNonce_checkPow (bits : ℕ) : (historyOps.checkPow bits).ReadsNonce := by
  rintro (_ | ⟨⟨b, d⟩, r⟩) x r' h
  · simp [historyOps] at h
  · change (nonceOf (b, d)).map (·, r) = some (x, r') at h
    rcases b with _ | _ | n
    · simp [nonceOf] at h
    · simp [nonceOf] at h
    · simp only [nonceOf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨n, d, by rw [h.2]⟩

/-- The commitment: a message. -/
def commitFam (sh : Whir.Shape) (κ : ℕ) : ChalSlots (commitWordSpec sh κ) :=
  fun ⟨0, _⟩ h ↦ nomatch h

private theorem pos_commitFam (sh : Whir.Shape) (κ : ℕ) : (commitFam sh κ).Pos :=
  fun ⟨0, _⟩ h ↦ nomatch h

variable (I : M3Instance)

/-- The challenges of the front of the compiled protocol. -/
def frontFam (sh : Whir.Shape) (κ : ℕ) : ChalSlots (listBindingFrontSpec I sh κ) :=
  ChalSlots.append (ChalSlots.append (ChalSlots.append (ChalSlots.append (ChalSlots.append
    (ChalSlots.append (commitFam sh κ) (busFam I)) (tableFam I)) pubFam) (flockFam I I.flock))
    (ChalSlots.draw eSlot)) ChalSlots.empty

private theorem pos_frontFam (sh : Whir.Shape) (κ : ℕ) : (frontFam I sh κ).Pos :=
  pos_append (pos_append (pos_append (pos_append (pos_append (pos_append (pos_commitFam sh κ)
    (pos_busFam I)) (pos_tableFam I)) pos_pubFam) (pos_flockFam I _)) (pos_draw eSlot_pos))
    pos_empty

private theorem readsWell_frontDec (h : Bus.Conditions I) (input : I.Stmt) (ann : List E)
    {sh : Whir.Shape} {κ : ℕ} (w₀ : KWord sh.ℓ (κ + sh.R) sh.t) :
    (frontDec I h input ann w₀).ReadsWell (frontFam I sh κ) fun _ ↦ false :=
  readsWell_append_none (readsWell_append_none (readsWell_append_none (readsWell_append_none
    (readsWell_append_none (readsWell_append_none
    (.of_squeezes (fun ⟨0, _⟩ h ↦ nomatch h) (blind_single (blind_commitSlot ann w₀)))
    fun _ ↦ readsWell_busDec I) fun _ ↦ readsWell_tableDec I _) fun _ ↦ readsWell_pubDec _)
    fun _ ↦ readsWell_flockDec I _) fun _ ↦ readsWell_sample) fun _ ↦ readsWell_empty

/-! ### WHIR's levels -/

/-- Every level's positions fit its squeezes: one position to a squeeze at least, and one
position at least. -/
def posOk : {sh : Whir.Shape} → {κ : ℕ} → Ladder sh κ → Bool
  | _, _, .last sh nf => decide (0 < 192 / (nf + 1 + sh.R)) && decide (0 < sh.t)
  | _, _, @Ladder.cons sh sh' κ' L =>
    decide (0 < 192 / (Kap sh' κ' + sh.R)) && decide (0 < sh.t) && posOk L

theorem posOk_last {sh : Whir.Shape} {nf : ℕ} (h : posOk (.last sh nf) = true) :
    0 < 192 / (nf + 1 + sh.R) ∧ 0 < sh.t := by
  simpa only [posOk, Bool.and_eq_true, decide_eq_true_eq] using h

theorem posOk_cons {sh sh' : Whir.Shape} {κ' : ℕ} {L : Ladder sh' κ'}
    (h : posOk (Ladder.cons sh L) = true) :
    (0 < 192 / (Kap sh' κ' + sh.R) ∧ 0 < sh.t) ∧ posOk L = true := by
  simpa only [posOk, Bool.and_eq_true, decide_eq_true_eq] using h

private theorem posSqueezes_pos (b : ℕ) {t : ℕ} (ht : 0 < t) : 0 < posSqueezes b t t := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [posSqueezes]
  omega

/-- The challenges of a level, before those of the levels after it. -/
def levelFam (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step} (hK : 0 < 192 / (Kap sh' κ' + sh.R))
    (rest : SeqSlots k) : SeqSlots (levelSteps sh sh' κ' k) :=
  (ChalSlots.draw eSlot, ChalSlots.rounds eSlot 2 sh.lm1, ChalSlots.say _, ChalSlots.sayO _,
    ChalSlots.draws eSlot (Kap sh' κ'), ChalSlots.say _, ChalSlots.say _, ChalSlots.say _,
    ChalSlots.draw (positionsUSlot _ _ hK), ChalSlots.draw eSlot, ChalSlots.empty, ChalSlots.say _,
    ChalSlots.empty, rest)

/-- The nonce flags of a level: its nonce. -/
def levelFlags (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step} (rest : SeqFlags k) :
    SeqFlags (levelSteps sh sh' κ' k) :=
  (fun _ ↦ false, fun _ ↦ false, fun _ ↦ false, fun _ ↦ false, fun _ ↦ false, fun _ ↦ false,
    fun _ ↦ false, fun _ ↦ true, fun _ ↦ false, fun _ ↦ false, fun _ ↦ false, fun _ ↦ false,
    fun _ ↦ false, rest)

private theorem pos_levelFam (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step}
    (hK : 0 < 192 / (Kap sh' κ' + sh.R)) (ht : 0 < sh.t) {rest : SeqSlots k} (hr : rest.Pos) :
    (levelFam sh sh' κ' hK rest).Pos :=
  ⟨pos_draw eSlot_pos, pos_rounds eSlot_pos _ _, pos_say _, pos_sayO _, pos_draws eSlot_pos _,
    pos_say _, pos_say _, pos_say _, pos_draw (posSqueezes_pos _ ht), pos_draw eSlot_pos,
    pos_empty, pos_say _, pos_empty, hr⟩

private theorem readsWell_levelDec (sh sh' : Whir.Shape) (κ' : ℕ) {k : List Step}
    (hK : 0 < 192 / (Kap sh' κ' + sh.R)) (σ : Thunk E × Thunk (Vector E 3))
    (w : WordOf sh (Kap sh' κ')) (next : WordOf sh' κ')
    {cont : Thunk E × Thunk (Vector E 3) → SeqDecoder Reading k} {rest : SeqSlots k}
    {restN : SeqFlags k} (hc : ∀ σ', (cont σ').ReadsWell rest restN) :
    (levelDec sh sh' κ' σ w next cont).ReadsWell (levelFam sh sh' κ' hK rest)
      (levelFlags sh sh' κ' restN) := by
  dsimp only [levelDec, levelFam, levelFlags]
  exact ⟨readsWell_sample, fun _ ↦
    ⟨readsWell_roundsDec 2 (fun _ ↦ none) _ sh.lm1, fun _ ↦
    ⟨readsWell_say (blind_polySlot _ _ _), fun _ ↦
    ⟨readsWell_sayO ((historyOps_blind ⟨0, 0, 0, fun _ ↦ 0⟩).nextRoot.mapM _), fun _ ↦
    ⟨readsWell_samples _, fun _ ↦
    ⟨readsWell_say blind_nextScalar, fun _ ↦
    ⟨readsWell_say (blind_polySlot _ _ _), fun _ ↦
    ⟨readsWell_nonce (blind_checkPow _) (readsNonce_checkPow _), fun _ ↦
    ⟨readsWell_draw (readsSqueezes_positionsSlot _ _ hK) (blind_positionsSlot _ _), fun _ ↦
    ⟨readsWell_sample, fun _ ↦
    ⟨readsWell_empty, fun _ ↦
    ⟨readsWell_say (blind_polySlot _ _ _), fun _ ↦
    ⟨readsWell_empty, fun _ ↦ hc _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The challenges of the last level. -/
def finalFam (sh : Whir.Shape) (nf : ℕ) (hK : 0 < 192 / (nf + 1 + sh.R)) :
    SeqSlots (finalSteps sh nf) :=
  (ChalSlots.draw eSlot, ChalSlots.rounds eSlot 2 sh.lm1, ChalSlots.say _, ChalSlots.say _,
    ChalSlots.say _, ChalSlots.draw (positionsUSlot _ _ hK), ChalSlots.draw eSlot, ChalSlots.empty,
    ChalSlots.say _, ChalSlots.empty, ChalSlots.draw eSlot, ChalSlots.rounds eSlot 2 nf, ⟨⟩)

/-- The nonce flags of the last level: its nonce. -/
def finalFlags (sh : Whir.Shape) (nf : ℕ) : SeqFlags (finalSteps sh nf) :=
  (fun _ ↦ false, fun _ ↦ false, fun _ ↦ false, fun _ ↦ false, fun _ ↦ true, fun _ ↦ false,
    fun _ ↦ false, fun _ ↦ false, fun _ ↦ false, fun _ ↦ false, fun _ ↦ false, fun _ ↦ false, ⟨⟩)

private theorem pos_finalFam (sh : Whir.Shape) (nf : ℕ) (hK : 0 < 192 / (nf + 1 + sh.R))
    (ht : 0 < sh.t) : (finalFam sh nf hK).Pos :=
  ⟨pos_draw eSlot_pos, pos_rounds eSlot_pos _ _, pos_say _, pos_say _, pos_say _,
    pos_draw (posSqueezes_pos _ ht), pos_draw eSlot_pos, pos_empty, pos_say _, pos_empty,
    pos_draw eSlot_pos, pos_rounds eSlot_pos _ _, trivial⟩

private theorem readsWell_finalDec (sh : Whir.Shape) (nf : ℕ) (hK : 0 < 192 / (nf + 1 + sh.R))
    (σ : Thunk E × Thunk (Vector E 3)) (w : WordOf sh (nf + 1)) :
    (finalDec sh nf σ w).ReadsWell (finalFam sh nf hK) (finalFlags sh nf) := by
  dsimp only [finalDec, finalFam, finalFlags]
  exact ⟨readsWell_sample, fun _ ↦
    ⟨readsWell_roundsDec 2 (fun _ ↦ none) _ sh.lm1, fun _ ↦
    ⟨readsWell_say (blind_polySlot _ _ _), fun _ ↦
    ⟨readsWell_say (blind_vecSlot _), fun _ ↦
    ⟨readsWell_nonce (blind_checkPow _) (readsNonce_checkPow _), fun _ ↦
    ⟨readsWell_draw (readsSqueezes_positionsSlot _ _ hK) (blind_positionsSlot _ _), fun _ ↦
    ⟨readsWell_sample, fun _ ↦
    ⟨readsWell_empty, fun _ ↦
    ⟨readsWell_say (blind_polySlot _ _ _), fun _ ↦
    ⟨readsWell_empty, fun _ ↦
    ⟨readsWell_sample, fun _ ↦
    ⟨readsWell_roundsDec 2 (fun _ ↦ none) _ nf, fun _ ↦ trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The challenges of a chain of levels. -/
def ladderFam : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) → posOk L = true →
    SeqSlots L.steps
  | _, _, .last sh nf, h => finalFam sh nf (posOk_last h).1
  | _, _, @Ladder.cons sh sh' κ' L, h =>
    levelFam sh sh' κ' (posOk_cons h).1.1 (ladderFam L (posOk_cons h).2)

/-- The nonce flags of a chain of levels: every level's nonce. -/
def ladderFlags : {sh : Whir.Shape} → {κ : ℕ} → (L : Ladder sh κ) → SeqFlags L.steps
  | _, _, .last sh nf => finalFlags sh nf
  | _, _, @Ladder.cons sh sh' κ' L => levelFlags sh sh' κ' (ladderFlags L)

private theorem pos_ladderFam : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (h : posOk L = true),
    (ladderFam L h).Pos
  | _, _, .last sh nf, h => pos_finalFam sh nf _ (posOk_last h).2
  | _, _, @Ladder.cons sh sh' κ' L, h =>
    pos_levelFam sh sh' κ' _ (posOk_cons h).1.2 (pos_ladderFam L _)

private theorem readsWell_ladderDec : ∀ {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ)
    (h : posOk L = true) (σ : Thunk E × Thunk (Vector E 3)) (w : WordOf sh κ) (ws : L.Words),
    (ladderDec L σ w ws).ReadsWell (ladderFam L h) (ladderFlags L)
  | _, _, .last sh nf, _, σ, w, _ => readsWell_finalDec sh nf _ σ w
  | _, _, @Ladder.cons sh sh' κ' L, _, σ, w, ws =>
    readsWell_levelDec sh sh' κ' _ σ w ws.1 fun σ' ↦ readsWell_ladderDec L _ σ' ws.1 ws.2

/-- The challenges of WHIR's opening. -/
def whirFam {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) (h : posOk L = true) :
    SeqSlots (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps) :=
  (ChalSlots.empty, ChalSlots.say _, ladderFam L h)

/-- The nonce flags of WHIR's opening. -/
def whirFlags {sh : Whir.Shape} {κ : ℕ} (L : Ladder sh κ) :
    SeqFlags (.skip :: .msg (SumcheckRound.Message E 2) :: L.steps) :=
  (fun _ ↦ false, fun _ ↦ false, ladderFlags L)

/-- **The challenges of the compiled protocol** on a chain of levels whose positions fit. -/
def compiledFam (c : Chain) (h : posOk c.ladder = true) :
    ChalSlots (listBindingSpec I c.sh c.κ c.ladder) :=
  ChalSlots.append (frontFam I c.sh c.κ) (whirFam c.ladder h).toFam

/-- The nonce flags of the compiled protocol: WHIR's nonces. -/
def compiledFlags (c : Chain) :
    Fin (1 + busRounds I + tableRounds I + 2 + flockRounds I I.flock + 1 + 0 +
      seqRounds (.skip :: .msg (SumcheckRound.Message E 2) :: c.ladder.steps)) → Bool :=
  Fin.append (fun _ ↦ false) (whirFlags c.ladder).toFlags

theorem pos_compiledFam (c : Chain) (h : posOk c.ladder = true) : (compiledFam I c h).Pos :=
  pos_append (pos_frontFam I _ _) (SeqSlots.Pos.toFam ⟨pos_empty, pos_say _, pos_ladderFam _ h⟩)

/-- **The decoder of the compiled protocol reads well.** -/
theorem readsWell_compiledDec (hI : Bus.Conditions I) (input : I.Stmt) (ann : List E) (c : Chain)
    (W : Words c) (h : posOk c.ladder = true) :
    (compiledDec I hI input ann c W).ReadsWell (compiledFam I c h) (compiledFlags I c) :=
  readsWell_append (readsWell_frontDec I hI input ann W.level0) fun _ ↦
    SeqDecoder.ReadsWell.toDecoder
      ⟨readsWell_empty, fun _ ↦ ⟨readsWell_say (blind_polySlot _ _ _), fun _ ↦
        readsWell_ladderDec c.ladder h _ _ _⟩⟩

end Compiled

end LeanVmSlots

end

end LeanerVM.Protocol
