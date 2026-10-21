/-
  LeanVM.Guest.B1.Tables.FlockLoopsM

  `verify_flock`'s Fiat-Shamir blocks and loops over a hash model: the chain's steps answered by
  the model, the sumcheck rounds' states over the model's hash made total.
-/

module

public import LeanVM.Guest.B1.Tables.FlockLoops
public import LeanVM.Guest.B1.Tables.GkrBaseM

/-!
# `__loop81` and `__loop82` over a hash model

`FlockLoops.lean` over a hash model `M`. The zerocheck's and the lincheck's rounds are a chain of
states, each computed from the last (`scStep`, `lcStep`); over the model the same chain is
computed with the model's hash made total (`hashT`, `obsCvT`, `sqCvT`: the answer, `default`
where there is none), and the steps the guest checks are answered, so they are the total
function's values (`obsCvT_eq`, `sqCvT_eq`). `RoundOk M g cv` says a round's three hashes (its
two words absorbed, the squeeze) are answered.

* `fsNext_chainM`, `squeeze_chainM`: an `fs_next` and a `squeeze` from a known state, under
  `M.sem`;
* `L81BodyM`, `loop81_stepM`: `__loop81`'s squeeze, answered, at the total `sqCvT`;
* `scStepT`, `lcStepT`, `L82BodyM`, `loop82_stepM`: `__loop82`'s round, answered (`RoundOk`), at
  the total `scStepT`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-! ## The model's hash, made total -/

/-- The model's answer, `default` where it gives none. -/
def hashT (M : HashModel) (x : List UInt8) : Digest := (M.H x).getD default

/-- The chain after absorbing a word, over the model's total hash (`obsCv`). -/
def obsCvT (M : HashModel) (cv : Digest) (x : E) : Digest := hashT M (digestBytes cv ++ blockOf x 1)

/-- The chain after a squeeze, over the model's total hash (`sqCv`). -/
def sqCvT (M : HashModel) (cv : Digest) : Digest := hashT M (digestBytes cv ++ blockOf 0 2)

variable {M : HashModel}

/-- An answered absorption is the total one. -/
theorem obsCvT_eq {cv : Digest} {x : E} {d : Digest} (h : obsCvM M cv x = some d) :
    obsCvT M cv x = d := by
  unfold obsCvT hashT
  unfold obsCvM at h
  rw [h]; rfl

/-- An answered squeeze is the total one. -/
theorem sqCvT_eq {cv d : Digest} (h : sqCvM M cv = some d) : sqCvT M cv = d := by
  unfold sqCvT hashT
  unfold sqCvM at h
  rw [h]; rfl

/-! ## The Fiat-Shamir blocks as steps, under the model -/

section
variable {C : CallRel} {rd : Reader} {σ : Val}

/-- **An `fs_next` from a known state** under `M.sem` (`fsNext_chain`): the word read, and the new
state the model's answer. -/
theorem fsNext_chainM {s0 s1 cur : V} {j b : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (fsNextT s0 s1 cur j b) True kret) {cv : Digest}
    (hcv : (σ s0, σ s1) = digestScalars cv) :
    LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ d, obsCvM M cv (σ (.n b)) = some d ∧
      (σ (.n (b + 13)), σ (.n (b + 14))) = digestScalars d := by
  obtain ⟨⟨hl, cv', d, hcv', hd, e⟩, -⟩ := holdsB_fsNextT s0 s1 cur j b h
  obtain rfl := digestScalars_injective (hcv'.symm.trans hcv)
  have e12 := e 12 (by omega) (by omega)
  have e13 := e 13 (by omega) (by omega)
  rw [show b + 1 + 12 = b + 13 by omega] at e12
  rw [show b + 1 + 13 = b + 14 by omega] at e13
  exact ⟨hl, d, hd, by rw [e12, e13]; rfl⟩

/-- **A `squeeze` from a known state** under `M.sem` (`squeeze_chain`). -/
theorem squeeze_chainM {s0 s1 : V} {b : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (squeezeT s0 s1 b) True kret) {cv : Digest}
    (hcv : (σ s0, σ s1) = digestScalars cv) :
    ∃ d, sqCvM M cv = some d ∧ (σ (.n (b + 5)), σ (.n (b + 6))) = digestScalars d ∧
      σ (.n (b + 13)) = challengeOf d := by
  obtain ⟨⟨cv', d, hcv', hd, e⟩, -⟩ := holdsB_squeezeT s0 s1 b h
  obtain rfl := digestScalars_injective (hcv'.symm.trans hcv)
  exact ⟨d, hd, by rw [e 5 (by omega), e 6 (by omega)]; rfl, e 13 (by omega)⟩

end

/-! ## The rounds over the total hash -/

/-- One round of the equality-mode sumcheck over the model's total hash (`scStep`). -/
def scStepT (M : HashModel) (e : E) (g : E × E) (s : E × Digest) : E × E × Digest :=
  let cv := obsCvT M (obsCvT M s.2 g.1) g.2
  let chi := challengeOf (sqCvT M cv)
  (chi, s.1 + e * (g.1 + g.2) + chi * (g.1 + chi * g.2), sqCvT M cv)

/-- One round of the plain-mode sumcheck over the model's total hash (`lcStep`). -/
def lcStepT (M : HashModel) (g : E × E) (s : E × Digest) : E × E × Digest :=
  let cv := obsCvT M (obsCvT M s.2 g.1) g.2
  let r := challengeOf (sqCvT M cv)
  (r, g.1 + r * (s.1 + g.2 + r * g.2), sqCvT M cv)

variable (M) in
/-- **A round's hashes are answered**: from the state `cv`, the two words `g` absorbed and the
squeeze. -/
def RoundOk (g : E × E) (cv : Digest) : Prop :=
  obsCvM M cv g.1 = some (obsCvT M cv g.1) ∧
    obsCvM M (obsCvT M cv g.1) g.2 = some (obsCvT M (obsCvT M cv g.1) g.2) ∧
    sqCvM M (obsCvT M (obsCvT M cv g.1) g.2) = some (sqCvT M (obsCvT M (obsCvT M cv g.1) g.2))

/-- A round's checked hashes are answered, and are the total ones. -/
theorem roundOk_of {g : E × E} {cv d1 d2 d3 : Digest} (h1 : obsCvM M cv g.1 = some d1)
    (h2 : obsCvM M d1 g.2 = some d2) (h3 : sqCvM M d2 = some d3) :
    RoundOk M g cv ∧ d1 = obsCvT M cv g.1 ∧ d2 = obsCvT M (obsCvT M cv g.1) g.2 ∧
      d3 = sqCvT M (obsCvT M (obsCvT M cv g.1) g.2) := by
  have e1 := (obsCvT_eq h1).symm
  subst e1
  have e2 := (obsCvT_eq h2).symm
  subst e2
  have e3 := (sqCvT_eq h3).symm
  subst e3
  exact ⟨⟨h1, h2, h3⟩, rfl, rfl, rfl⟩

/-! ## `__loop81` over the model -/

variable (M) in
/-- `__loop81` at `x` over the model (`L81Body`): the squeeze answered, at the total `sqCvT`. -/
def L81BodyM (rd : Reader) (pts zr x : E) : Prop :=
  ∃ cv : Digest, LoadHolds rd (pts * (x * x)) 0 (digestScalars cv).1 ∧
    LoadHolds rd (pts * (x * x)) 1 (digestScalars cv).2 ∧ sqCvM M cv = some (sqCvT M cv) ∧
    LoadHolds rd (zr * x) 0 (challengeOf (sqCvT M cv)) ∧
    LoadHolds rd (pts * (x * x)) 2 (digestScalars (sqCvT M cv)).1 ∧
    LoadHolds rd (pts * (x * x)) 3 (digestScalars (sqCvT M cv)).2

/-- **`__loop81` over the model**, one iteration, forward (`loop81_step`). -/
theorem loop81_stepM (rd : Reader) (N pts zr : E) (d : ℕ) (x : E)
    (h : coreProgram.relNB M.sem rd (d + 1) "__loop81" (x :: [N, pts, zr]) []) :
    L81BodyM M rd pts zr x ∧ IsInK (x * gen + N) ∧
      (x * gen + N ≠ 0 → coreProgram.relNB M.sem rd d "__loop81" (x * gen :: [N, pts, zr]) []) := by
  rw [relNB_succ_iff find_loop81, show Fn.params Data.core140 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    core140_body, l81Body] at h
  obtain ⟨σ, hp, hb⟩ := h
  rw [holdsListB_append, holdsListB_append] at hb
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, and_true,
    word_gen] at hb
  obtain ⟨h4, h5, l6, l7, hsq⟩ := hb
  obtain ⟨⟨cv, dq, hcv, hdq, e⟩, h22, l21, l13, l14, h23, h24, h25, h26, h27, hK, hcall⟩ :=
    holdsB_squeezeT _ _ _ hsq
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hp
  have eq := (sqCvT_eq hdq).symm
  subst eq
  have e5 : σ (.n 13) = (digestScalars (sqCvT M cv)).1 := e 5 (by omega)
  have e6 : σ (.n 14) = (digestScalars (sqCvT M cv)).2 := e 6 (by omega)
  have e13 : σ (.n 21) = challengeOf (sqCvT M cv) := e 13 (by omega)
  rw [h4] at h5
  rw [h5] at l6 l7 l13 l14
  rw [h22, e13] at l21
  rw [e5] at l13
  rw [e6] at l14
  refine ⟨⟨cv, ?_, ?_, hdq, l21, l13, l14⟩, by rwa [h25, h24, h23] at hK, fun hne => ?_⟩
  · rw [show σ (.n 6) = (digestScalars cv).1 from congrArg Prod.fst hcv] at l6; exact l6
  · rw [show σ (.n 7) = (digestScalars cv).2 from congrArg Prod.snd hcv] at l7; exact l7
  · have := hcall (by rwa [h25, h24, h23])
    rwa [h27, h26] at this

/-! ## `__loop82` over the model -/

variable (M) in
/-- `__loop82` at `x` over the model (`L82Body`): the round answered (`RoundOk`), at the total
`scStepT`. -/
def L82BodyM (rd : Reader) (rnd zr chis x : E) : Prop :=
  ∃ (cv : Digest) (cur claim e g1 g2 : E),
    LoadHolds rd (rnd * (x * x * (x * x))) 0 (digestScalars cv).1 ∧
    LoadHolds rd (rnd * (x * x * (x * x))) 1 (digestScalars cv).2 ∧
    LoadHolds rd (rnd * (x * x * (x * x))) 2 cur ∧ LoadHolds rd (rnd * (x * x * (x * x))) 3 claim ∧
    LoadHolds rd (zr * x) 6 e ∧ LoadHolds rd cur 0 g1 ∧ LoadHolds rd cur 1 g2 ∧
    RoundOk M (g1, g2) cv ∧
    LoadHolds rd (chis * x) 0 (scStepT M e (g1, g2) (claim, cv)).1 ∧
    LoadHolds rd (rnd * (x * x * (x * x))) 4
      (digestScalars (scStepT M e (g1, g2) (claim, cv)).2.2).1 ∧
    LoadHolds rd (rnd * (x * x * (x * x))) 5
      (digestScalars (scStepT M e (g1, g2) (claim, cv)).2.2).2 ∧
    LoadHolds rd (rnd * (x * x * (x * x))) 6 (cur * gen ^ 2) ∧
    LoadHolds rd (rnd * (x * x * (x * x))) 7 (scStepT M e (g1, g2) (claim, cv)).2.1

set_option maxHeartbeats 1000000 in
/-- **`__loop82` over the model**, one iteration, forward (`loop82_step`). -/
theorem loop82_stepM (rd : Reader) (N rnd zr chis : E) (d : ℕ) (x : E)
    (h : coreProgram.relNB M.sem rd (d + 1) "__loop82" (x :: [N, rnd, zr, chis]) []) :
    L82BodyM M rd rnd zr chis x ∧ IsInK (x * gen + N) ∧
      (x * gen + N ≠ 0 →
        coreProgram.relNB M.sem rd d "__loop82" (x * gen :: [N, rnd, zr, chis]) []) := by
  rw [relNB_succ_iff find_loop82,
    show Fn.params Data.core141 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl, core141_body,
    l82Body] at h
  obtain ⟨σ, hp, hb⟩ := h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hp
  simp only [holdsListB_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons,
    List.map_nil, and_true, word_gen, word_four'] at hb
  obtain ⟨h5, h6, h7, l8, l9, h10, l11, l12, hb⟩ := hb
  obtain ⟨⟨l13, cv, d1, hcv, hd1, e1⟩, hb⟩ := holdsB_fsNextT _ _ _ _ _ hb
  obtain ⟨⟨l28, cv2, d2, hcv2, hd2, e2⟩, hb⟩ := holdsB_fsNextT _ _ _ _ _ hb
  obtain ⟨l43, h44, h45, h46, hb⟩ := hb
  obtain ⟨⟨cv3, d3, hcv3, hd3, e3⟩, h61, l60, l52, l53, h62, h63, l63, h64, h65, h66, h67, l67,
    h68, h69, h70, h71, h72, hK, hcall⟩ := holdsB_squeezeT _ _ _ hb
  -- the chain
  have c2 : cv2 = d1 := by
    have a12 : σ (.n 26) = _ := e1 12 (by omega) (by omega)
    have a13 : σ (.n 27) = _ := e1 13 (by omega) (by omega)
    exact digestScalars_injective (hcv2.symm.trans (by rw [a12, a13]; rfl))
  have c3 : cv3 = d2 := by
    have a12 : σ (.n 41) = _ := e2 12 (by omega) (by omega)
    have a13 : σ (.n 42) = _ := e2 13 (by omega) (by omega)
    exact digestScalars_injective (hcv3.symm.trans (by rw [a12, a13]; rfl))
  subst c2 c3
  obtain ⟨hok, rfl, rfl, rfl⟩ := roundOk_of (g := (σ (.n 13), σ (.n 28))) hd1 hd2 hd3
  have s5 : σ (.n 52) = (digestScalars (sqCvT M (obsCvT M (obsCvT M cv (σ (.n 13)))
      (σ (.n 28))))).1 := e3 5 (by omega)
  have s6 : σ (.n 53) = (digestScalars (sqCvT M (obsCvT M (obsCvT M cv (σ (.n 13)))
      (σ (.n 28))))).2 := e3 6 (by omega)
  have s13 : σ (.n 60) = challengeOf (sqCvT M (obsCvT M (obsCvT M cv (σ (.n 13)))
      (σ (.n 28)))) := e3 13 (by omega)
  rw [h6, h5] at h7
  rw [h7] at l8 l9 l12 l43 l52 l53 l63 l67
  rw [h10] at l11
  rw [h61] at l60
  have hst : scStepT M (σ (.n 11)) (σ (.n 13), σ (.n 28)) (σ (.n 43), cv) =
      (σ (.n 60), σ (.n 67), sqCvT M (obsCvT M (obsCvT M cv (σ (.n 13))) (σ (.n 28)))) := by
    refine Prod.ext s13.symm (Prod.ext ?_ rfl)
    show σ (.n 43) + σ (.n 11) * (σ (.n 13) + σ (.n 28)) +
        challengeOf (sqCvT M (obsCvT M (obsCvT M cv (σ (.n 13))) (σ (.n 28)))) *
          (σ (.n 13) + challengeOf (sqCvT M (obsCvT M (obsCvT M cv (σ (.n 13))) (σ (.n 28)))) *
            σ (.n 28)) = σ (.n 67)
    rw [h67, h66, h65, h64, h46, h45, h44, s13]
  refine ⟨⟨cv, σ (.n 12), σ (.n 43), σ (.n 11), σ (.n 13), σ (.n 28), ?_, ?_, l12, l43, l11, l13,
    l28, hok, ?_, ?_, ?_, ?_, ?_⟩, by rwa [h70, h69, h68] at hK, fun hne => ?_⟩
  · rw [show σ (.n 8) = (digestScalars cv).1 from congrArg Prod.fst hcv] at l8; exact l8
  · rw [show σ (.n 9) = (digestScalars cv).2 from congrArg Prod.snd hcv] at l9; exact l9
  · rw [hst]; exact l60
  · rw [hst, ← s5]; exact l52
  · rw [hst, ← s6]; exact l53
  · rw [h63, h62] at l63; exact l63
  · rw [hst]; exact l67
  · have := hcall (by rwa [h70, h69, h68])
    rwa [h72, h71] at this

end
end LeanVM.Guest.B1
