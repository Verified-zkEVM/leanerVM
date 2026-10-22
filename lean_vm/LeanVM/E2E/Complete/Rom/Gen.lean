/-
  LeanVM.E2E.Complete.Rom.Gen

  T6-prob's inhabitant: a generator that runs honest leanXMSS key generation, signs the zero
  message, and outputs the leaf holding that claim directly; its outputs are valid at every hash
  agreeing with the oracle's log, and within the limits.
-/

module

public import LeanVM.E2E.Complete.Count.Final
public import LeanVM.E2E.Complete.Witness
public import LeanVM.E2E.Reduction.XmssBound

/-!
# The inhabitant generator

`docs/roadmap/t6-prob.md` §4.6. `xmssLeafGen : OracleComp HashSpec (Option HonestTree)`: leanXMSS's
key generation from the zero seed (`Seeded.keygenFromSeed`), then one signature at leaf index `0`
on the zero message (`Seeded.sign`), every leanXMSS hash a query of the game's oracle read as
`256` bits (`xgImpl`); the leaf `xmssLeaf pk σ` holding the claim `(pk, 0)` by `σ`, or nothing if
signing fails.

* **Correctness at every hash** (`xg_correct`). For every `f : HashInput → HashOutput`, the
  signature the signer outputs with every hash answered by `f` verifies under the key that key
  generation outputs with `f`: the one-time signature's chains walked on reach the key's chain ends
  (`xgEv_chainWalk_comp`), so its leaf is the tree's leaf `0`; the path of key `0` folds it into the
  tree's root (`xgEv_treeFold`); the bottom root is what the top layer signed, and the top root the
  key's.
* **The bridge** (`xmssLeafGen_spec`). On a reachable outcome of the run against `Rom.loggedRO`,
  the outcome is the generator's value at every hash `Ht` agreeing with the final log
  (`simulateQ_look_of_mem_support`, `simulateQ_id_of_look`), which is the deterministic run at
  `digestBits ∘ Ht` (`simulateQ_xgImpl`); there the signature verifies (`xg_correct`), and
  `xmssVerifyWith (some ∘ Ht)` is that verification (`xmssVerifyWith_eq_simulateQ`,
  `simulateQ_pure_comp`). So the leaf is valid at `Ht`.
* **The limits** (`xmssLeaf_limits`): a leaf with one leanXMSS claim held directly is within the
  deployed limits and the budget, for every key and signature (`End.work` reads only shapes; the
  budget is `Witness.lean`'s kernel evaluation); hence `WithinLimitsBudget` at every hash
  (`withinLimitsBudget_xmssLeaf`).
* **The queries** (`isTotalQueryBound_xmssLeafGen`): at most `xmssKeygenBound + xmssSignBound`.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleSpec OracleComp

@[expose] public section

/-! ## The generator -/

/-- **leanXMSS's hash as a query of the game's oracle**: the digest read as `256` bits. -/
def xgImpl : QueryImpl LeanXmss.HashSpec (OracleComp HashSpec) :=
  fun x ↦ Node.digestBits <$> queryH x

/-- Leaf index `0`. -/
def xgIdx0 : LeanXmss.LeafIndex := ⟨0, Nat.two_pow_pos _⟩

/-- One-time key `0`. -/
def xgKey0 : LeanXmss.KeyIndex := ⟨0, Nat.two_pow_pos _⟩

/-- **Honest leanXMSS**: key generation from the zero seed, then a signature at leaf index `0` on
the zero message; the key and the signature, if signing succeeds. -/
def xgCore : OracleComp LeanXmss.HashSpec (Option (LeanXmss.PublicKey × LeanXmss.Signature)) := do
  let k ← LeanXmss.Seeded.keygenFromSeed 0
  let σ? ← (LeanXmss.Seeded.sign k.2 xgIdx0 0 : OracleComp LeanXmss.HashSpec _)
  return σ?.map (k.1, ·)

/-- **The leaf** holding the claim `(pk, 0)` directly by `σ`. -/
def xmssLeaf (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) : HonestTree :=
  .node ⟨[(pk, 0)], [], []⟩ [.direct σ] [] [] []

/-- **The inhabitant generator**: honest leanXMSS key generation and one signature on the zero
message, every hash a query of the game's oracle; the leaf holding the claim directly. -/
noncomputable def xmssLeafGen : OracleComp HashSpec (Option HonestTree) :=
  (fun r ↦ r.map fun p ↦ xmssLeaf p.1 p.2) <$> simulateQ xgImpl xgCore

/-! ## Deterministic runs -/

/-- A hash's answers as leanXMSS's `256`-bit outputs. -/
def xgBits (Ht : Bytes → Digest) : LeanXmss.HashInput → LeanXmss.HashOutput :=
  fun x ↦ Node.digestBits (Ht x)

/-- The run of a leanXMSS computation with every hash answered by `f`. -/
def xgEv {α : Type} (f : LeanXmss.HashInput → LeanXmss.HashOutput)
    (oa : OracleComp LeanXmss.HashSpec α) : α :=
  (simulateQ (fun x ↦ (pure (f x) : Id LeanXmss.HashOutput)) oa).run

section Ev

variable (f : LeanXmss.HashInput → LeanXmss.HashOutput)

@[simp] theorem xgEv_pure {α : Type} (a : α) : xgEv f (pure a) = a := rfl

@[simp] theorem xgEv_bind {α β : Type} (oa : OracleComp LeanXmss.HashSpec α)
    (g : α → OracleComp LeanXmss.HashSpec β) : xgEv f (oa >>= g) = xgEv f (g (xgEv f oa)) := by
  simp only [xgEv, simulateQ_bind]
  rfl

@[simp] theorem xgEv_map {α β : Type} (oa : OracleComp LeanXmss.HashSpec α) (g : α → β) :
    xgEv f (g <$> oa) = g (xgEv f oa) := by
  simp only [xgEv, simulateQ_map]
  rfl

@[simp] theorem xgEv_oracleHash (x : LeanXmss.HashInput) :
    xgEv f (LeanXmss.Concrete.oracleHash x : OracleComp LeanXmss.HashSpec _) = f x := by
  change xgEv f (liftM (LeanXmss.HashSpec.query x) >>= fun o ↦ pure o) = f x
  simp only [xgEv, simulateQ_bind, simulateQ_query, simulateQ_pure]
  rfl

theorem xgEv_sequenceFin {α : Type} : ∀ {n : ℕ} (c : Fin n → OracleComp LeanXmss.HashSpec α),
    xgEv f (LeanXmss.Concrete.sequenceFin c) = fun i ↦ xgEv f (c i)
  | 0, _ => funext fun i ↦ i.elim0
  | n + 1, c => by
    simp only [LeanXmss.Concrete.sequenceFin, xgEv_bind, xgEv_pure,
      xgEv_sequenceFin fun i : Fin n ↦ c i.succ]
    funext i
    cases i using Fin.cases <;> rfl

end Ev

/-! ## The game's run at a hash is the deterministic run -/

/-- **The translation run at a total hash** is the deterministic run at its bits. -/
theorem simulateQ_xgImpl {α : Type} (Ht : Bytes → Digest) :
    ∀ oa : OracleComp LeanXmss.HashSpec α,
      simulateQ (fun x ↦ (pure (Ht x) : Id Digest)) (simulateQ xgImpl oa) =
        xgEv (xgBits Ht) oa := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_bind, xgEv_bind]
    change simulateQ _ (Node.digestBits <$> queryH t) >>= _ = _
    rw [simulateQ_map]
    exact ih _

/-- **Verification at a total hash** is the deterministic verification at its bits. -/
theorem xmssVerifyWith_some_eq_xgEv (Ht : Bytes → Digest) (pk : LeanXmss.PublicKey)
    (msg : LeanXmss.Message) (σ : LeanXmss.Signature) :
    xmssVerifyWith (fun x ↦ some (Ht x)) pk msg σ =
      some (xgEv (xgBits Ht) (LeanXmss.Concrete.verify pk msg σ)) := by
  rw [xmssVerifyWith_eq_simulateQ]
  exact simulateQ_pure_comp (n := Option) (xgBits Ht : QueryImpl LeanXmss.HashSpec Id) _

/-! ## leanXMSS's correctness at every hash -/

section Correct

open LeanXmss LeanXmss.Concrete LeanXmss.Seeded

variable (f : HashInput → HashOutput)

/-- Two chain walks in a row are one: `a` steps from the start, then `b` more. -/
theorem xgEv_chainWalk_comp (p : PublicParameter) (lay : Layer) (key : KeyIndex)
    (i : ChainIndex) (a : ℕ) (v : LeanXmss.Digest) : ∀ b : ℕ,
    xgEv f (chainWalk p lay key i a b (xgEv f (chainWalk p lay key i 0 a v))) =
      xgEv f (chainWalk p lay key i 0 (a + b) v)
  | 0 => rfl
  | b + 1 => by
    rw [← Nat.add_assoc]
    simp only [chainWalk, xgEv_bind]
    rw [xgEv_chainWalk_comp p lay key i a v b]
    simp only [Nat.zero_add]

theorem xg_keyAt (lay : Layer) : keyAt xgIdx0 lay = xgKey0 :=
  Fin.ext (Nat.zero_div _)

/-- The randomizer trials: the opening's digest decodes, and its values are the chains walked
`enc i` steps from the key's secrets. -/
theorem xgEv_otsSignFrom (p : PublicParameter) (lay : Layer) (key : KeyIndex) (seed : MasterSeed)
    (msg : HashInput) (base : Randomness) : ∀ (attempts trial : ℕ) r vals,
    xgEv f (otsSignFrom p lay key seed msg base attempts trial) = some (r, vals) →
      ∃ enc, Codeword.decode (xgEv f (messageDigest p lay key msg r)) = some enc ∧
        vals = fun i ↦ xgEv f (chainWalk p lay key i 0 (enc i).val
          (xgEv f (otsSecrets p lay key seed) i))
  | 0, _, _, _, h => by simp [otsSignFrom] at h
  | attempts + 1, trial, r, vals, h => by
    simp only [otsSignFrom, xgEv_bind] at h
    split at h
    · rename_i enc hd
      simp only [xgEv_bind, xgEv_pure, xgEv_sequenceFin, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨enc, hd, rfl⟩
    · exact xgEv_otsSignFrom p lay key seed msg base attempts (trial + 1) r vals h

/-- **A one-time signature recovers its key's leaf**: the tree's leaf `0`. -/
theorem xgEv_otsLeaf (p : PublicParameter) (lay : Layer) (seed : MasterSeed) (msg : HashInput)
    (r : Randomness) (vals : ChainIndex → LeanXmss.Digest)
    (h : xgEv f (otsSign p lay xgKey0 seed msg) = some (r, vals)) :
    xgEv f (otsLeaf p lay xgKey0 msg r vals) = some (xgEv f (treeNode p lay seed 0 0)) := by
  simp only [otsSign, xgEv_bind] at h
  obtain ⟨enc, hd, rfl⟩ := xgEv_otsSignFrom f p lay xgKey0 seed msg _ _ _ r vals h
  have hk : (⟨0 % lifetime, Nat.mod_lt _ (by decide)⟩ : KeyIndex) = xgKey0 := Fin.ext (Nat.zero_mod _)
  simp only [otsLeaf, treeNode, oneTimePublicKey, recoverChain, xgEv_bind, xgEv_pure, hd,
    xgEv_sequenceFin, hk]
  congr 2
  refine congrArg _ (funext fun i ↦ ?_)
  rw [xgEv_chainWalk_comp]
  have := (enc i).isLt
  have he : (enc i).val + (chainLength - 1 - (enc i).val) = chainLength - 1 := by
    simp only [chainLength, winternitzBits] at this ⊢
    omega
  rw [he]

/-- The path of key `0`: at every level, the node `1`. -/
theorem xgEv_treePath (p : PublicParameter) (lay : Layer) (seed : MasterSeed) :
    xgEv f (treePath p lay seed xgKey0) = fun level ↦ xgEv f (treeNode p lay seed level.val 1) := by
  simp only [treePath, xgEv_sequenceFin, xgKey0, Nat.zero_div]
  rfl

/-- **The path of key `0` folds its leaf into the tree's nodes `0`.** -/
theorem xgEv_treeFold (p : PublicParameter) (lay : Layer) (seed : MasterSeed) (L : ℕ)
    (hL : L ≤ layerHeight) :
    xgEv f (treeFold p lay xgKey0 (xgEv f (treePath p lay seed xgKey0)) L
      (xgEv f (treeNode p lay seed 0 0))) = xgEv f (treeNode p lay seed L 0) := by
  induction L with
  | zero => rw [treeFold, xgEv_pure]
  | succ L ih =>
    rw [treeFold, xgEv_bind, ih (Nat.le_of_succ_le hL)]
    have hL' : L < layerHeight := hL
    have h0 : (xgKey0.val / 2 ^ (L + 1)) = 0 := Nat.zero_div _
    have hb : xgKey0.val.testBit L = false := Nat.zero_testBit L
    simp only [hL', ↓reduceDIte, h0, hb, Bool.false_eq_true, ↓reduceIte, xgEv_treePath]
    rw [treeNode]
    simp only [xgEv_bind, Nat.mul_zero, Nat.zero_add]

/-- **A layer's signature by key `0` reaches the layer's root**, node `0` at the top level. -/
theorem xgEv_layerRoot (sk : SecretKey) (lay : Layer) (msg : HashInput) (part : LayerSignature)
    (h : xgEv f (signLayer sk lay xgKey0 msg) = some part) :
    xgEv f (layerRoot sk.parameter lay xgKey0 msg part) =
      some (xgEv f (treeNode sk.parameter lay sk.seed layerHeight 0)) := by
  simp only [signLayer, xgEv_bind] at h
  rcases ho : xgEv f (otsSign sk.parameter lay xgKey0 sk.seed msg) with _ | ⟨r, vals⟩
  · simp [ho] at h
  · simp only [ho, xgEv_bind, xgEv_pure, Option.some.injEq] at h
    subst h
    simp only [layerRoot, xgEv_bind]
    rw [xgEv_otsLeaf f _ _ _ _ _ _ ho]
    simp only [xgEv_bind, xgEv_pure]
    rw [xgEv_treeFold f _ _ _ _ le_rfl]

/-- Key generation at `f`: the scheme's seed `S`, the parameter `P`, and the top tree's root. -/
theorem xgEv_keygen (s : MasterSeed) (S : MasterSeed) (P : PublicParameter)
    (hS : f (seedHashInput s) = S) (hP : truncateHash (f (keygenHashInput 0 .parameter S)) = P) :
    xgEv f (keygenFromSeed s) =
      (⟨xgEv f (treeNode P topLayer S layerHeight 0), P⟩,
        ⟨S, P, xgEv f (treeNode P topLayer S layerHeight 0)⟩) := by
  have e : (keygenFromSeed s : OracleComp LeanXmss.HashSpec _) = (do
      let seed ← schemeSeed s
      let parameter ← deriveKey 0 .parameter seed
      let root ← treeNode parameter topLayer seed layerHeight 0
      pure ((⟨root, parameter⟩ : PublicKey), (⟨seed, parameter, root⟩ : SecretKey))) := rfl
  rw [e]
  generalize layerHeight = L
  have hs : xgEv f (schemeSeed s : OracleComp LeanXmss.HashSpec MasterSeed) = S :=
    (xgEv_oracleHash f _).trans hS
  have hp : xgEv f (deriveKey 0 .parameter S : OracleComp LeanXmss.HashSpec LeanXmss.Digest) = P := by
    unfold deriveKey
    rw [xgEv_bind, xgEv_oracleHash, xgEv_pure, hP]
  rw [xgEv_bind, hs, xgEv_bind, hp, xgEv_bind, xgEv_pure]

/-- A signature at leaf index `0`: both layers' signatures by key `0`, the top one of the bottom
tree's root. -/
theorem xgEv_sign (sk : SecretKey) (σ : Signature) (h : xgEv f (sign sk xgIdx0 0) = some σ) :
    ∃ bottom top, xgEv f (signLayer sk bottomLayer xgKey0 (bytesLE 32 (0 : Message))) = some bottom ∧
      xgEv f (signLayer sk topLayer xgKey0
        (bytesLE 16 (xgEv f (treeNode sk.parameter bottomLayer sk.seed layerHeight 0)))) = some top ∧
      σ = ⟨xgIdx0, fun lay ↦ if lay = bottomLayer then bottom else top⟩ := by
  have hv : (keyAt xgIdx0 topLayer).val = 0 := Nat.zero_div _
  rw [sign] at h
  generalize layerHeight = L at h ⊢
  rw [xgEv_bind, hv, xg_keyAt, xg_keyAt] at h
  split at h
  · rename_i bottom hb
    simp only [xgEv_bind] at h
    split at h
    · rename_i top ht
      simp only [xgEv_pure, Option.some.injEq] at h
      exact ⟨bottom, top, hb, ht, h.symm⟩
    · simp at h
  · simp at h

/-- Verification of a signature at leaf index `0` from its layers' roots. -/
theorem xgEv_verify (pk : PublicKey) (bottom top : LayerSignature) (rb : LeanXmss.Digest)
    (hb : xgEv f (layerRoot pk.parameter bottomLayer xgKey0 (bytesLE 32 (0 : Message)) bottom) =
      some rb)
    (ht : xgEv f (layerRoot pk.parameter topLayer xgKey0 (bytesLE 16 rb) top) = some pk.root) :
    xgEv f (Concrete.verify pk 0 ⟨xgIdx0, fun lay ↦ if lay = bottomLayer then bottom else top⟩) =
      true := by
  have htb : (topLayer = bottomLayer) = False := by simp [topLayer, bottomLayer]
  rw [Concrete.verify]
  simp only [xgEv_bind, xg_keyAt, ↓reduceIte, htb]
  rw [hb]
  simp only [xgEv_bind]
  rw [ht]
  simp only [xgEv_pure, decide_true]

/-- **leanXMSS is correct at every hash**: the signature honest leanXMSS outputs verifies under
its key, with every hash answered by `f`. -/
theorem xg_correct (pk : PublicKey) (σ : Signature) (h : xgEv f xgCore = some (pk, σ)) :
    xgEv f (Concrete.verify pk 0 σ) = true := by
  generalize hS : f (seedHashInput 0) = S
  generalize hP : truncateHash (f (keygenHashInput 0 .parameter S)) = P
  generalize hR : xgEv f (treeNode P topLayer S layerHeight 0) = R
  have hk := xgEv_keygen f 0 S P hS hP
  rw [hR] at hk
  rw [xgCore, xgEv_bind, hk, xgEv_bind, xgEv_pure, Option.map_eq_some_iff] at h
  obtain ⟨σ', hσ, hpk⟩ := h
  rw [Prod.mk.injEq] at hpk
  obtain ⟨rfl, rfl⟩ := hpk
  obtain ⟨bottom, top, hb, ht, rfl⟩ := xgEv_sign f ⟨S, P, R⟩ _ hσ
  have hb' := xgEv_layerRoot f ⟨S, P, R⟩ bottomLayer _ bottom hb
  have ht' := xgEv_layerRoot f ⟨S, P, R⟩ topLayer _ top ht
  exact xgEv_verify f ⟨R, P⟩ bottom top _ hb' (ht'.trans (congrArg some hR))

end Correct

/-! ## The generator's outputs -/

/-- **A leaf holding one leanXMSS claim directly is within the deployed limits and the budget**,
for every key and signature. -/
theorem xmssLeaf_limits (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    End.Limits ⟨⟨[(pk, 0)], [], []⟩, leafDefer⟩ ⟨[], [.direct σ], [], [], noHints⟩ ∧
      B2C.b2cBudget'.size
        (End.work ⟨⟨[(pk, 0)], [], []⟩, leafDefer⟩ ⟨[], [.direct σ], [], [], noHints⟩) ≤ 2 ^ 28 := by
  have hcov : End.coverage ⟨⟨[(pk, 0)], [], []⟩, leafDefer⟩ ⟨[], [.direct σ], [], [], noHints⟩ = 1 := by
    simp [End.coverage, Hints.plan, Hints.direct, Hints.takeSlots, Hints.takeSlot,
      Hints.takeSlotsAll]
  have hwork : End.work ⟨⟨[(pk, 0)], [], []⟩, leafDefer⟩ ⟨[], [.direct σ], [], [], noHints⟩ =
      ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ := by
    rw [End.work, hcov]
    rfl
  refine ⟨{ stackLog := fun c hc ↦ absurd hc List.not_mem_nil
            stream := fun c hc ↦ absurd hc List.not_mem_nil
            directDa := Nat.zero_le _
            xmssHeld := fun x ↦ by simp [Hints.direct]
            sphincsHeld := fun x ↦ by simp
            daHeld := fun x ↦ by simp
            children := Nat.zero_le _
            daRoots := ⟨Nat.zero_le _, fun c hc ↦ absurd hc List.not_mem_nil⟩
            lists := fun c hc ↦ absurd hc List.not_mem_nil
            coverage := by rw [hcov]; norm_num
            nonempty := Nat.one_pos }, ?_⟩
  rw [hwork]
  refine (End.sizeOf_mono words_wTree instrs_wTree).trans ?_
  simp only [End.sizeOf, instrsBound, Memory.logMem, Nat.clog_pow 2 _ one_lt_two, guest_logSize,
    minLogMem]
  norm_num

/-- **The leaf is within the deployed limits and the budget at every hash.** -/
theorem withinLimitsBudget_xmssLeaf (H : Bytes → Digest) (ρ pfuel : ℕ) (pk : LeanXmss.PublicKey)
    (σ : LeanXmss.Signature) : (xmssLeaf pk σ).WithinLimitsBudget H ρ pfuel := by
  rw [xmssLeaf, HonestTree.WithinLimitsBudget, HonestTree.allNodes_node]
  refine ⟨?_, fun k hk ↦ absurd hk List.not_mem_nil⟩
  intro kos hkos hd hdef
  obtain ⟨rfl, rfl⟩ := leaf_outs hkos hdef
  exact xmssLeaf_limits pk σ

/-- **The leaf of a verifying signature is valid.** -/
theorem valid_xmssLeaf {H : Bytes → Digest} {pk : LeanXmss.PublicKey} {σ : LeanXmss.Signature}
    (h : xmssVerifyWith (fun x ↦ some (H x)) pk 0 σ = some true) : (xmssLeaf pk σ).Valid H := by
  refine ⟨?_, fun c hc ↦ absurd hc List.not_mem_nil⟩
  rw [xmssLeaf, HonestTree.allNodes_node]
  exact ⟨⟨.cons h .nil, .nil, .nil⟩, fun k hk ↦ absurd hk List.not_mem_nil⟩

theorem xmssLeaf_size (pk : LeanXmss.PublicKey) (σ : LeanXmss.Signature) :
    (xmssLeaf pk σ).size ≤ 1 := by
  rw [xmssLeaf, HonestTree.size]
  simp

/-- **The generator's outputs are leaves valid at every hash agreeing with its log.** -/
theorem xmssLeafGen_spec :
    ∀ z ∈ support ((simulateQ loggedRO xmssLeafGen).run []), ∀ T, z.1 = some T →
      ∃ pk σ, T = .node ⟨[(pk, 0)], [], []⟩ [.direct σ] [] [] [] ∧
        ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) → T.Valid Ht := by
  intro z hz T hT
  have hrun := (simulateQ_look_of_mem_support xmssLeafGen [] z hz).2 z.2 (List.prefix_refl _)
  have hId : ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) →
      (xgEv (xgBits Ht) xgCore).map (fun p ↦ xmssLeaf p.1 p.2) = z.1 := by
    intro Ht hHt
    have := simulateQ_id_of_look z.2 Ht hHt xmssLeafGen z.1 hrun
    rw [xmssLeafGen, simulateQ_map, simulateQ_xgImpl] at this
    exact this
  -- the key and signature, read at one hash agreeing with the log
  let H0 : Bytes → Digest := fun x ↦ (look z.2 x).getD 0
  have hH0 : ∀ x u, look z.2 x = some u → H0 x = u := fun x u h ↦ by simp [H0, h]
  have h0 := hId H0 hH0
  rw [hT, Option.map_eq_some_iff] at h0
  obtain ⟨⟨pk, σ⟩, -, rfl⟩ := h0
  refine ⟨pk, σ, rfl, fun Ht hHt ↦ ?_⟩
  have h1 := hId Ht hHt
  rw [hT, Option.map_eq_some_iff] at h1
  obtain ⟨⟨pk', σ'⟩, hc, he⟩ := h1
  have he' : pk' = pk ∧ σ' = σ := by
    simp only [xmssLeaf, HonestTree.node.injEq, Claims.mk.injEq, List.cons.injEq, Prod.mk.injEq,
      Holder.direct.injEq] at he
    exact ⟨he.1.1.1.1, he.2.1.1⟩
  obtain ⟨rfl, rfl⟩ := he'
  apply valid_xmssLeaf
  rw [xmssVerifyWith_some_eq_xgEv, xg_correct _ _ _ hc]

/-- **The generator's outputs are valid and within the limits**: every output is a leaf (size at
most `1`), valid and within the deployed limits and the budget at every hash agreeing with the
oracle's log (`ValidGen`'s fields but the prover's query count). -/
theorem xmssLeafGen_valid (ρ pfuel : ℕ) :
    ∀ z ∈ support ((simulateQ loggedRO xmssLeafGen).run []), ∀ T, z.1 = some T →
      T.size ≤ 1 ∧ ∀ Ht : Bytes → Digest, (∀ x u, look z.2 x = some u → Ht x = u) →
        T.Valid Ht ∧ T.WithinLimitsBudget Ht ρ pfuel := by
  intro z hz T hT
  obtain ⟨pk, σ, rfl, hv⟩ := xmssLeafGen_spec z hz T hT
  exact ⟨xmssLeaf_size pk σ, fun Ht hHt ↦ ⟨hv Ht hHt, withinLimitsBudget_xmssLeaf Ht ρ pfuel pk σ⟩⟩

/-! ## The generator's queries -/

/-- The translation keeps a query bound: one leanXMSS hash is one query. -/
theorem isTotalQueryBound_simulateQ_xgImpl {α : Type} :
    ∀ (oa : OracleComp LeanXmss.HashSpec α) (n : ℕ), IsTotalQueryBound oa n →
      IsTotalQueryBound (simulateQ xgImpl oa) n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x => intro n _; trivial
  | query_bind t k ih =>
    intro n h
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [simulateQ_bind]
    change IsTotalQueryBound ((Node.digestBits <$> queryH t) >>= fun u ↦ simulateQ xgImpl (k u)) n
    rw [bind_map_left]
    exact isTotalQueryBound_query_bind_iff.mpr ⟨h.1, fun u ↦ ih _ _ (h.2 _)⟩

/-- **The generator's queries**: key generation's and one signature's. -/
theorem isTotalQueryBound_xmssLeafGen :
    IsTotalQueryBound xmssLeafGen (E2E.xmssKeygenBound + E2E.xmssSignBound) := by
  have hc : IsTotalQueryBound xgCore (E2E.xmssKeygenBound + (E2E.xmssSignBound + 0)) :=
    isTotalQueryBound_bind (E2E.keygenFromSeed_isTotalQueryBound 0) fun k ↦
      isTotalQueryBound_bind (E2E.sign_isTotalQueryBound _ _ _) fun _ ↦ isQueryBound_pure _ _ _ _
  rw [Nat.add_zero] at hc
  unfold xmssLeafGen
  rw [map_eq_bind_pure_comp]
  exact (isTotalQueryBound_bind (n₂ := 0) (isTotalQueryBound_simulateQ_xgImpl _ _ hc)
    fun _ ↦ isQueryBound_pure _ _ _ _).mono (Nat.add_zero _).le

/-- The generator's query bound: `2^33 + 53,739,486`. -/
theorem xmssLeafGen_queries_eq : E2E.xmssKeygenBound + E2E.xmssSignBound = 2 ^ 33 + 53739486 := by
  rw [E2E.xmssKeygenBound_eq, E2E.xmssSignBound_eq]
  norm_num

end
end LeanVM.E2E.Complete
