/-
  LeanVM.Protocol.EndToEnd.Blind.Complete

  Perfect completeness of the Flock-blind verifier V°: from a stack satisfying the leanISA
  relation without Flock and honest padding, an honest strategy wins every interactive run of
  `blindProgram`, and its compiled proof is accepted by V° for every hash, when the proof-of-work
  searches succeed.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Theorem
public import LeanVM.Protocol.EndToEnd.Blind.Relation
public import LeanVM.Spec.Ideal.Blind

/-!
# Completeness of V°

V° (`LeanVM.Spec.Ideal.Blind`, `docs/roadmap/e2e-security.md` D3) is the deployed verifier with the
lincheck's terminal check deleted. Its honest prover is the deployed one (`Complete/Assemble.lean`)
with Flock replaced:

* **Flock without its terminal checks nothing but the slices.** The zerocheck and the lincheck's
  sumcheck only read and sample (`sumcheckRoundPoly` derives one coefficient per round from the
  claim and checks nothing), so any messages follow them: `replay` sends zeros along a program
  that only reads and samples (`RS`), and returns its result (`follows_replay`). The slices are the
  true slices of the stack's `QFLOCK` region at the returned point (`flockSlice`), which ring
  switching binds to the committed stack (`follows_ringSwitch`, unchanged). `hFlockBlind`,
  `follows_hFlockBlind`.
* **The other phases need no Flock relation.** The bus, the table sumcheck and the public input
  only read the constraints, the bus, the counts, the public lines and the padding: their
  deployed simulations, restated from `M3HoldsBlind` and `PaddingHonest`
  (`follows_verifyBusBalanceBlind`, `follows_tablePhaseBlind`, `follows_publicInputPhaseBlind`).

`runI_blindProgram`: for a stack satisfying `M3HonestBlind` (`M3HoldsBlind` and honest padding) at
admissible sizes and a valid rate, the honest strategy wins every interactive run of
`blindProgram`, with well-shaped words; `exists_prove_verifyBlindWith`: for every hash `H`, its
compiled proof is accepted by V° (`verifyBlindWith`) as soon as every proof-of-work search finds a
nonce below the fuel. No hypothesis on the Flock region: in particular no `WalkFaithful`.
-/

namespace LeanVM.Protocol.EndToEnd.Blind

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Blake2sHash

@[expose] public section

/-! ## Programs that only read and sample -/

/-- **`p` only reads and samples, and returns a value satisfying `Q`**, whatever it reads and
samples. -/
def RS {α : Type} (Q : α → Prop) : Prog α → Prop
  | .ret a => Q a
  | .read k => ∀ x, RS Q (k x)
  | .sample k => ∀ c, RS Q (k c)
  | _ => False

/-- The script sending zeros along a program that only reads and samples, returning its result.
-/
def replay {α : Type} [Inhabited α] : Prog α → Script α
  | .ret a => .ret a
  | .read k => .send 0 (replay (k 0))
  | .sample k => .sample fun c ↦ replay (k c)
  | _ => .ret default

/-- **Zeros follow a program that only reads and samples**, to its result. -/
theorem follows_replay {α : Type} [Inhabited α] {Q : α → Prop} (cs : Commits) :
    ∀ (p : Prog α), RS Q p → Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ Q b) (replay p) p cs
  | .ret _, h => ⟨rfl, rfl, h⟩
  | .read k, h => follows_replay cs (k 0) (h 0)
  | .sample k, h => fun c ↦ follows_replay cs (k c) (h c)
  | .fail, h => absurd h id
  | .grind _ _, h => absurd h id
  | .commit _ _ _, h => absurd h id
  | .query _ _ _, h => absurd h id

/-- Reading and sampling compose. -/
theorem RS.bind {α β : Type} {Q' : α → Prop} {Q : β → Prop} {f : α → Prog β}
    (hf : ∀ a, Q' a → RS Q (f a)) : ∀ {p : Prog α}, RS Q' p → RS Q (p.bind f)
  | .ret a, h => hf a h
  | .read _, h => fun x ↦ RS.bind hf (h x)
  | .sample _, h => fun c ↦ RS.bind hf (h c)
  | .fail, h => absurd h id
  | .grind _ _, h => absurd h id
  | .commit _ _ _, h => absurd h id
  | .query _ _ _, h => absurd h id

/-- A weaker postcondition. -/
theorem RS.mono {α : Type} {Q Q' : α → Prop} (hQ : ∀ a, Q a → Q' a) :
    ∀ {p : Prog α}, RS Q p → RS Q' p
  | .ret a, h => hQ a h
  | .read _, h => fun x ↦ RS.mono hQ (h x)
  | .sample _, h => fun c ↦ RS.mono hQ (h c)
  | .fail, h => absurd h id
  | .grind _ _, h => absurd h id
  | .commit _ _ _, h => absurd h id
  | .query _ _ _, h => absurd h id

/-- A return satisfying the postcondition. -/
theorem rs_ret {α : Type} {Q : α → Prop} {a : α} (h : Q a) : RS Q (Prog.ret a) := h

/-- Reading a scalar, then a program for every scalar. -/
theorem rs_readE_bind {α : Type} {Q : α → Prop} {f : E → Prog α} (h : ∀ x, RS Q (f x)) :
    RS Q (Prog.readE.bind f) := fun x ↦ h x

/-- Sampling a challenge, then a program for every challenge. -/
theorem rs_sampleE_bind {α : Type} {Q : α → Prop} {f : E → Prog α} (h : ∀ x, RS Q (f x)) :
    RS Q (Prog.sampleE.bind f) := fun x ↦ h x

theorem rs_readN (n : ℕ) : RS (fun l : List E ↦ l.length = n) (Prog.readN n) := by
  induction n with
  | zero => exact rfl
  | succ n ih =>
    simp only [Prog.readN, Prog.bind_eq]
    exact rs_readE_bind fun x ↦ RS.bind (Q' := fun l : List E ↦ l.length = n)
      (fun l hl ↦ rs_ret (show (x :: l).length = n + 1 by simp [hl])) ih

theorem rs_sampleN (n : ℕ) : RS (fun l : List E ↦ l.length = n) (Prog.sampleN n) := by
  induction n with
  | zero => exact rfl
  | succ n ih =>
    simp only [Prog.sampleN, Prog.bind_eq]
    exact rs_sampleE_bind fun x ↦ RS.bind (Q' := fun l : List E ↦ l.length = n)
      (fun l hl ↦ rs_ret (show (x :: l).length = n + 1 by simp [hl])) ih

theorem rs_sumcheckRoundPoly (count : ℕ) (claim : E) (eq : Option E) :
    RS (fun _ ↦ True) (sumcheckRoundPoly count claim eq) := by
  cases eq with
  | none =>
    simp only [sumcheckRoundPoly, Prog.bind_eq]
    exact rs_readE_bind fun _ ↦ RS.bind (fun _ _ ↦ trivial) (rs_readN _)
  | some e =>
    simp only [sumcheckRoundPoly, Prog.bind_eq]
    exact RS.bind (fun _ _ ↦ trivial) (rs_readN _)

/-- A sumcheck only reads and samples; its point has a coordinate per round. -/
theorem rs_sumcheck (count : ℕ) :
    ∀ (rounds : List (Option E)) (claim : E),
      RS (fun r : List E × E ↦ r.1.length = rounds.length) (sumcheck claim count rounds)
  | [], _ => rfl
  | e :: es, claim => by
    simp only [sumcheck, Prog.bind_eq]
    refine RS.bind (fun msg _ ↦ ?_) (rs_sumcheckRoundPoly count claim e)
    refine rs_sampleE_bind fun c ↦ ?_
    refine RS.bind (Q' := fun r : List E × E ↦ r.1.length = es.length) (fun r hr ↦ ?_)
      (rs_sumcheck count es _)
    exact rs_ret (show (c :: r.1).length = es.length + 1 by simp [hr])

attribute [local irreducible] RS in
/-- The zerocheck only reads and samples; its point has the program's coordinates. -/
theorem rs_verifyFlockZerocheck (logN : ℕ) :
    RS (fun zc : ZerocheckResult ↦
        zc.chi.length = fixedChallenges.length + (logN - flockKSkip - fixedChallenges.length))
      (verifyFlockZerocheck logN) := by
  unfold verifyFlockZerocheck
  simp only [Prog.bind_eq]
  refine RS.bind (Q' := fun l : List E ↦ l.length = logN - flockKSkip - fixedChallenges.length)
    (fun sampled hs ↦ ?_) (rs_sampleN _)
  refine RS.bind (Q' := fun l : List E ↦ l.length = kBits) (fun _ _ ↦ ?_) (rs_readN _)
  refine rs_sampleE_bind fun zSkip ↦ ?_
  refine RS.bind (Q' := fun r : List E × E ↦
      r.1.length = ((fixedChallenges ++ sampled).map some).length) (fun r hr ↦ ?_)
    (rs_sumcheck 3 _ _)
  obtain ⟨chi, running⟩ := r
  refine rs_readE_bind fun vA ↦ rs_readE_bind fun vB ↦ rs_ret ?_
  show chi.length = _
  rw [hr, List.length_map, List.length_append, hs]

/-! ## Flock, blind -/

instance : Inhabited ZerocheckResult := ⟨⟨0, [], 0, 0, 0⟩⟩

variable (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- The true slices of the stack's `QFLOCK` region at a point. -/
noncomputable def slicesAt (point : List E) : List E :=
  (List.range 64).map fun i ↦ flockSlice prog s q i point

/-- **The honest prover of V°'s Flock phase**: zeros along the zerocheck and the lincheck's
sumcheck, then the true slices at the returned point. -/
noncomputable def hFlockBlind : Script (List E × List E) :=
  (replay (verifyFlockZerocheck (flockLogN prog s))).bind fun zc ↦
  Script.sampleE.bind fun alpha ↦
  (replay (sumcheck (zc.vA + alpha * zc.vB + alpha ^ 2 * zc.vC + alpha ^ 3) 3
    (List.replicate flockNumLincheckRounds none))).bind fun x ↦
  (Script.sendList (slicesAt prog s q (x.1.reverse ++ zc.chi.drop flockNumLincheckRounds))).bind
    fun _ ↦
  .ret (x.1.reverse ++ zc.chi.drop flockNumLincheckRounds,
    slicesAt prog s q (x.1.reverse ++ zc.chi.drop flockNumLincheckRounds))

attribute [local irreducible] Follows in
/-- **The honest prover follows V°'s Flock phase** to its true result (`FlockGood`): the point of
the region's `8 + τ` coordinates, and the true slices there. -/
theorem follows_hFlockBlind (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ FlockGood prog s q b) (hFlockBlind prog s q)
      (verifyFlockBlind (flockLogN prog s)) cs := by
  unfold hFlockBlind verifyFlockBlind verifyFlockLincheckBlind
  refine Follows.bind (fun cs₁ zc zc' h ↦ ?_) _ _ _
    (follows_replay cs _ (rs_verifyFlockZerocheck (flockLogN prog s)))
  obtain ⟨rfl, rfl, hchi⟩ := h
  rw [flockLogN_sub] at hchi
  refine Follows.bind (fun cs₂ a b h ↦ ?_) _ _ _ (Follows.sampleE_sampleE cs₁)
  obtain ⟨rfl, rfl⟩ := h
  refine Follows.bind (fun cs₃ x x' h ↦ ?_) _ _ _
    (follows_replay cs₂ _ (rs_sumcheck 3 (List.replicate flockNumLincheckRounds none) _))
  obtain ⟨rfl, rfl, hx⟩ := h
  rw [List.length_replicate] at hx
  have hlen : (slicesAt prog s q (x.1.reverse ++ zc.chi.drop flockNumLincheckRounds)).length =
      kBits := by simp [slicesAt, kBits]
  rw [← hlen]
  refine Follows.bind (fun cs₄ _ sl h ↦ ?_) _ _ _ (Follows.sendList_readN cs₃ _)
  obtain ⟨rfl, rfl⟩ := h
  refine Follows.ret_ret ⟨rfl, rfl, ?_, rfl⟩
  have hn : flockNumLincheckRounds = 8 := by decide
  have hf : fixedChallenges.length = 7 := rfl
  have hr : (flockArgP prog s).nRand = s.τ 5 + 1 := rfl
  rw [List.length_append, List.length_reverse, List.length_drop, hx, hchi, hn, hf, hr]
  omega

/-! ## The other phases, without Flock's relation -/

/-- **The relation without Flock, with honest padding**: what V°'s honest prover needs. -/
def M3HonestBlind (I : M3Instance) (input : I.Stmt) (q : Column I.μ) : Prop :=
  M3HoldsBlind I input q ∧ I.PaddingHonest q

variable {prog s q}

attribute [local irreducible] Follows in
/-- The bus phase, from the relation without Flock (`follows_verifyBusBalance`'s proof, which
reads only the balance, the counts and the padding). -/
theorem follows_verifyBusBalanceBlind {input : PublicInput} (hq : M3HonestBlind (inst prog s) input q)
    (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ BusGood prog s q b) (hBus prog s q)
      (verifyBusBalance .computed (verifierLayout prog s)) cs := by
  obtain ⟨⟨-, hbal, hcnt, -⟩, hP⟩ := hq
  rw [verifyBusBalance_eq', busLayout_depth_verifier, hBus]
  refine Follows.bind (fun cs₁ a b h ↦ ?_) _ _ _ (Follows.sampleN_sampleN cs busBits)
  obtain ⟨rfl, rfl, hlen⟩ := h
  rw [hBusK1, busK1]
  refine Follows.bind (fun cs₂ c c' h ↦ ?_) _ _ _ (Follows.sampleE_sampleE cs₁)
  obtain ⟨rfl, rfl⟩ := h
  rw [hBusK2, busK2]
  refine Follows.bind (fun cs₃ g g' h ↦ ?_) _ _ _
    (follows_verifyGkrGrandProducts (busDepth prog s) _ _ _ (length_pushLeaves prog s q a c)
      (length_pullLeaves prog s q a c) (length_countLeaves prog s q)
      (prod_push_eq_pull prog s q hbal a hlen c) cs₂)
  obtain ⟨rfl, rfl, hcr, hpl, htv⟩ := h
  have hne : g.1 ≠ 0 := hcr ▸ prod_countLeaves_ne_zero prog s q hcnt
  rw [hBusK3, busK3]
  simp only [Prog.require, hne, ne_eq, not_false_eq_true, ↓reduceIte, Prog.ret_bind]
  refine Follows.bind (fun cs₄ _ mem h ↦ ?_) _ _ _
    (Follows.sendList_readN cs₃ (memVals prog s q g.2.1))
  obtain ⟨rfl, rfl⟩ := h
  refine Follows.bind (fun cs₅ _ mf h ↦ ?_) _ _ _ (Follows.sendE_readE _ cs₄)
  obtain ⟨rfl, rfl⟩ := h
  refine Follows.bind (fun cs₆ _ bf h ↦ ?_) _ _ _ (Follows.sendE_readE _ cs₅)
  obtain ⟨rfl, rfl⟩ := h
  have heq : honestBus prog s q a c g.2.1 = busOut (verifierLayout prog s) a c g.2.1 g.2.2
      (memVals prog s q g.2.1) (mfVal prog s q g.2.1) (bfVal prog s q g.2.1) := by
    rw [honestBus, htv]
    rfl
  exact Follows.ret_ret ⟨rfl, heq, heq ▸ busGood_honestBus prog s q hP a hlen c g.2.1 hpl⟩

/-- On a stack whose constraints vanish, `JUMP`'s constraints vanish on every row
(`consPart_rowEvals`, from the constraints alone). -/
theorem consPart_rowEvalsBlind (hc : (inst prog s).ConstraintsVanish q) (cp : List E)
    (y : Fin (2 ^ s.τ 4)) : consPart cp 4 (rowEvals prog s q 4 y) = 0 := by
  have h := pyConstraints_eval 4 (rowCell prog s q 4 y)
  have hz : ∀ x ∈ (LeanIsa.constraints (opIdx 4)).map
      (fun P ↦ ofK (P.eval (rowCell prog s q 4 y))), x = 0 := by
    intro x hx
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hx
    have hv : P.eval (rowCell prog s q 4 y) = 0 := hc (opIdx 4) P hP y
    rw [hv]
    simp
  simp only [consPart, ↓reduceIte]
  apply Complete.dot_eq_zero_of_forall
  rw [show jumpConstraints (rowEvals prog s q 4 y) =
    (tables.getD ((4 : Fin 6) : ℕ) default).constraints
      ((List.finRange (width (opIdx 4))).map fun i ↦ ofK (rowCell prog s q 4 y i)) from rfl, h]
  exact hz

open Finset in
-- The table heights are `Nat.clog` of the row counts, which unification unfolds.
set_option maxHeartbeats 800000 in
/-- The table phase, from vanishing constraints (`follows_tablePhase`'s proof). -/
theorem follows_tablePhaseBlind (hc : (inst prog s).ConstraintsVanish q)
    (bus : BusResult) (hb : BusGood prog s q bus) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ TrueClaims prog s q b) (hTable prog s q bus)
      (tablePhase (verifierLayout prog s) bus) cs := by
  unfold tablePhase tableSumcheck hTable
  simp only [Prog.bind_eq]
  refine Follows.bind (fun cs₁ xi xi' h ↦ ?_) _ _ _ (Follows.sampleE_sampleE cs)
  obtain ⟨rfl, rfl⟩ := h
  have hh : (verifierLayout prog s).tableLogHeights = tableLogs s := rfl
  have hfp : (fpOf xi).length = 3 := by
    simp only [fpOf, List.length_drop, powers, length_powersFrom]; omega
  rw [show (powers xi ((tables.map Table.nConstraints).sum + 3)).take
      (tables.map Table.nConstraints).sum = cpOf xi from rfl,
    show (powers xi ((tables.map Table.nConstraints).sum + 3)).drop
      (tables.map Table.nConstraints).sum = fpOf xi from rfl]
  have htarget : dot (fpOf xi) bus.totals = claimOf prog s q (cpOf xi) (fpOf xi) bus [] := by
    rw [claimOf]
    simp only [List.length_nil, Nat.sub_zero, List.reverse_nil, List.append_nil]
    exact (sum_summand prog s q hb (cpOf xi) (fpOf xi) hfp
      (consPart_rowEvalsBlind hc (cpOf xi))).symm
  rw [hh, htarget, Prog.bind_assoc]
  refine Follows.bind (fun cs₂ r r' h ↦ ?_) _ _ _
    (follows_sumcheck 4 (by norm_num) (claimOf prog s q (cpOf xi) (fpOf xi) bus)
      (List.replicate (nRounds s) none) [] cs₁ ?_ ?_)
  · obtain ⟨rfl, rfl, hlen, hfin⟩ := h
    simp only [List.length_replicate] at hlen
    simp only [List.nil_append] at hfin
    rw [rows_eq prog s q bus hb.forms_length, Prog.bind_assoc]
    have hcheck : (termsPure (cpOf xi) (fpOf xi) r.1.reverse
        (pairsAt prog s q bus r.1.reverse) 0 0 []).1 = r.2 := by
      rw [hfin, claimOf, hlen, Nat.sub_self, pow_zero, sum_range_one]
      rfl
    have hgood := trueClaims_append hb.claims
      (trueClaims_termsPure prog s q bus (cpOf xi) (fpOf xi) r.1.reverse
        (by rw [List.length_reverse, hlen]))
    have hP := width_pairsAt prog s q bus r.1.reverse
    generalize pairsAt prog s q bus r.1.reverse = P at hcheck hgood hP ⊢
    exact follows_tableTail bus.claims (cpOf xi) (fpOf xi) r.1.reverse r.2 P hP hcheck _ hgood cs₂
  · intro ext hext
    simp only [List.length_replicate] at hext
    exact polyLE_claimOf prog s q hb _ _ ext hext
  · intro ext hext
    simp only [List.length_replicate] at hext
    simp only [List.getElem_replicate, RoundSplit, List.nil_append]
    exact claimOf_split prog s q _ _ bus ext hext

/-- The public-input step, from the public lines (`follows_publicInputPhase`'s proof). -/
theorem follows_publicInputPhaseBlind {input : PublicInput}
    (hlines : (inst prog s).PublicLinesHold input q) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ TrueClaims prog s q b) (hPub prog s q)
      (Verifier.publicInputPhase (verifierLayout prog s) (publicDigest input)) cs := by
  have hl : ∀ l ∈ ((inst prog s).publicLines input).toList,
      ((inst prog s).column q l.col).values.get ⟨0, Nat.two_pow_pos _⟩ = l.cell0 ∧
        ((inst prog s).column q l.col).values.get ⟨1, Nat.one_lt_two_pow l.pos.ne'⟩ = l.cell1 :=
    hlines
  have h0 := hl _ (by simp [inst, leanIsaInstance, publicLines] : (⟨memCol 0, input.lanes 0,
    input.lanes 2, false, s.logMem_pos⟩ : PublicLine (shape prog s)) ∈ _)
  have h1 := hl _ (by simp [inst, leanIsaInstance, publicLines] : (⟨memCol 1, input.lanes 1,
    input.lanes 3, false, s.logMem_pos⟩ : PublicLine (shape prog s)) ∈ _)
  have h2 := hl _ (by simp [inst, leanIsaInstance, publicLines] : (⟨memCol 2, 0, 0, false,
    s.logMem_pos⟩ : PublicLine (shape prog s)) ∈ _)
  simp only at h0 h1 h2
  unfold Verifier.publicInputPhase hPub
  simp only [Prog.bind_eq]
  refine Follows.bind (fun cs₁ r r' hr ↦ ?_) _ _ _ (Follows.sampleE_sampleE cs)
  obtain ⟨rfl, rfl⟩ := hr
  have hz : ofK (0 : K) = 0 := map_zero (algebraMap K E)
  have hlimbs : (([0, 1, 2] : List (Fin 3)).map fun limb ↦
      multilinearEval [ofK ((digestScalars (publicDigest input)).1.limb limb),
        ofK ((digestScalars (publicDigest input)).2.limb limb)] [r]) =
      [memLine prog s q 0 r, memLine prog s q 1 r, memLine prog s q 2 r] := by
    simp only [List.map_cons, List.map_nil, digestScalars_publicDigest, PublicInput.word0,
      PublicInput.word1, limb_ofLimbs, memLine_eq, h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]
    simp only [multilinearEval, List.foldl, foldPairs, List.headD]
    refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
    all_goals (try simp [hz])
    all_goals ring
  simp only [Prog.pure_eq]
  refine ⟨rfl, ?_, ?_⟩
  · show publicClaims (verifierLayout prog s) r _ = List.zipWith _ _ _
    rw [hlimbs]
    rfl
  · intro cl hcl
    rw [hlimbs] at hcl
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at hcl
    rcases hcl with rfl | rfl | rfl
    · exact trueClaim_memLine prog s q 0 r _ rfl
    · exact trueClaim_memLine prog s q 1 r _ rfl
    · exact trueClaim_memLine prog s q 2 r _ rfl

/-! ## The whole program -/

variable (prog s) in
/-- **The honest run of V°**: announce, commit, the deployed bus, table and public-input
provers, the blind Flock prover, ring switching, the stacked opening. -/
noncomputable def honestRunBlind (ρ : ℕ) (q : Column (leanIsaμ prog s)) : Script Unit :=
  (Script.sendList (announce s ρ)).bind fun _ ↦
  (Script.commitS (stackWord (leanIsaμ prog s) q)).bind fun _ ↦
  (hBus prog s q).bind fun bus ↦
  (hTable prog s q bus).bind fun claims ↦
  (hPub prog s q).bind fun pub ↦
  (hFlockBlind prog s q).bind fun fl ↦
  (hRing fl.1 fl.2).bind fun rs ↦
  honestOpening (leanIsaμ prog s) ρ q (openingClaims prog s rs (claims ++ pub))

attribute [local irreducible] Follows in
/-- **The honest run follows `verifyExecutionBlind`**: every `require` passes, whatever the
challenges. -/
theorem follows_verifyExecutionBlind {input : PublicInput} {ρ : ℕ} (hs : s.Admissible prog)
    (hρ : validRate ρ) (hq : M3HonestBlind (inst prog s) input q) :
    Follows (fun _ _ _ ↦ True) (honestRunBlind prog s ρ q)
      (verifyExecutionBlind (bytecodeWords prog) (publicDigest input)) [] := by
  have hadm := whirAdmissible prog hs hρ
  unfold verifyExecutionBlind honestRunBlind
  simp only [Prog.bind_eq]
  refine Follows.bind (fun cs₁ _ b hb ↦ ?_) _ _ _ (follows_readSizes prog hs hρ [])
  obtain ⟨rfl, rfl⟩ := hb
  simp only [stackLog_verifierLayout]
  refine Follows.bind (fun cs₂ _ _ hc ↦ ?_) _ _ _ (follows_commitStack hadm q [])
  subst hc
  refine Follows.bind (fun cs₃ bus bus' hb ↦ ?_) _ _ _ (follows_verifyBusBalanceBlind hq _)
  obtain ⟨rfl, rfl, hbus⟩ := hb
  refine Follows.bind (fun cs₄ cl cl' hc ↦ ?_) _ _ _ (follows_tablePhaseBlind hq.1.1 bus hbus _)
  obtain ⟨rfl, rfl, htab⟩ := hc
  refine Follows.bind (fun cs₅ pub pub' hc ↦ ?_) _ _ _
    (follows_publicInputPhaseBlind hq.1.2.2.2 _)
  obtain ⟨rfl, rfl, hpub⟩ := hc
  refine Follows.bind (fun cs₆ fl fl' hc ↦ ?_) _ _ _ (follows_hFlockBlind prog s q _)
  obtain ⟨rfl, rfl, hfl⟩ := hc
  refine Follows.bind (fun cs₇ rs rs' hc ↦ ?_) _ _ _ (follows_ringSwitch fl hfl _)
  obtain ⟨rfl, rfl, hrh, hrm⟩ := hc
  have hall := trueClaims_append htab hpub
  refine (follows_verifyStackedOpening hadm q _ ?_ ?_)
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hrh
    · obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hc
      exact (hall cl hcl).holds
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hrm
    · obtain ⟨cl, hcl, rfl⟩ := List.mem_map.mp hc
      exact (hall cl hcl).multilinear

variable (prog s) in
/-- The honest strategy of V°: the replay of the honest run, then accept. -/
noncomputable def honestStrategyBlind (ρ : ℕ) (q : Column (leanIsaμ prog s)) : Strategy :=
  Strategy.ofScript (honestRunBlind prog s ρ q >>= fun _ ↦ Script.ret ()) 0

/-- **The honest strategy wins every interactive run of V°**, with well-shaped words. -/
theorem runI_blindProgram {input : PublicInput} {ρ : ℕ} (hs : s.Admissible prog)
    (hρ : validRate ρ) (hq : M3HonestBlind (inst prog s) input q) (chal : List Ev → E) :
    runI (blindProgram (bytecodeWords prog) (publicDigest input))
        (honestStrategyBlind prog s ρ q) chal = some true ∧
      shapedI (blindProgram (bytecodeWords prog) (publicDigest input))
        (honestStrategyBlind prog s ρ q) chal := by
  have hf : Follows (fun _ _ b ↦ b = true) (honestRunBlind prog s ρ q >>= fun _ ↦ Script.ret ())
      (blindProgram (bytecodeWords prog) (publicDigest input)) [] :=
    Follows.bind_of (follows_verifyExecutionBlind hs hρ hq) fun _ _ _ _ ↦ rfl
  obtain ⟨⟨b, hb, _, _, rfl⟩, hsh⟩ := runFrom_of_follows' (h₀ := [])
    (honestStrategyBlind prog s ρ q) chal (ofScript_agrees _ []) hf
  exact ⟨hb, hsh⟩

/-- **V° accepts the honest proof, for every hash**: the compiled honest strategy's proof, from
the deployed seed, as soon as every proof-of-work search finds its nonce below `fuel`. -/
theorem exists_prove_verifyBlindWith (H : Bytes → Digest) {input : PublicInput} {ρ : ℕ}
    (hs : s.Admissible prog) (hρ : validRate ρ) (hq : M3HonestBlind (inst prog s) input q)
    (fuel : ℕ)
    (hg : ∀ hist bits k cv,
      (blindProgram (bytecodeWords prog) (publicDigest input)).after hist = some (.grind bits k) →
        findNonce H bits cv fuel ≠ none) :
    ∃ π, prove H (blindProgram (bytecodeWords prog) (publicDigest input))
        (honestStrategyBlind prog s ρ q)
        (Id.run (seedWith H (bytecodeWords prog) (publicDigest input))) fuel = some π ∧
      Id.run (verifyBlindWith (m := Id) H (bytecodeWords prog) (publicDigest input) π) = true :=
  exists_prove_runProof H _ _ _ fuel (fun chal ↦ (runI_blindProgram hs hρ hq chal).1)
    (fun chal ↦ (runI_blindProgram hs hρ hq chal).2) hg

end
end LeanVM.Protocol.EndToEnd.Blind
