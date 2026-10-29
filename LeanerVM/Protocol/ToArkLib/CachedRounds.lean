/-
  LeanerVM.Protocol.ToArkLib.CachedRounds

  The rounds of a sumcheck with a cached honest prover: a cache per stage, from which the honest
  polynomial is read and which each challenge updates, and the cached prover of the rounds that
  carries it. Candidate for ArkLib.
-/

module

public import LeanerVM.Protocol.ToArkLib.CachedProver
public import LeanerVM.Protocol.ToArkLib.SumcheckRound

/-!
# Cached sumcheck rounds

The honest polynomial of round `j` is a function of the context and the challenges so far
(`SumcheckRound.Polys`), so a prover that computes it from scratch rebuilds, every round, what it
reads: a sumcheck's tables bound to the challenges, a product tree's level. A `RoundCache P m`
says what a prover may keep instead, up to stage `m`: a cache type per stage (`C`), what the
cache holds at the context and the challenges (`cache`), how the honest polynomial is read off it
(`msg`, which must give `P`), and how a challenge updates it (`step`, which must give the next
stage's cache). `cachedRounds` is then a cached prover of `rounds P wt m i j` (Component.Cached):
each round's polynomial read off the cache, the cache updated at each challenge, the cache of
stage `j` taken and that of stage `m` handed on. Nothing about the verifier changes.
-/

namespace LeanerVM.Protocol

open OracleComp OracleSpec ProtocolSpec

@[expose] public section

namespace SumcheckRound

variable {F : Type} [Field F] {X : Type} {ι : Type} {O : ι → Type} {W : Type} {d : ℕ}

/-- What the honest prover of a sumcheck keeps from one round to the next, up to stage `m`: a
cache per stage, read off for the honest polynomial and updated by each challenge. -/
structure RoundCache (P : Polys F X O W d) (m : ℕ) where
  /-- The cache's type at each stage. -/
  C : ℕ → Type
  /-- What the cache holds at the context and the challenges. -/
  cache : (j : ℕ) → Ctx X O W → Vector F j → C j
  /-- The honest polynomial, read off the cache. -/
  msg : (j : ℕ) → Ctx X O W → Vector F j → C j → Message F d
  /-- The cache after a challenge. -/
  step : (j : ℕ) → Ctx X O W → Vector F j → C j → F → C (j + 1)
  /-- The polynomial read off the cache is the honest one. -/
  msg_eq : ∀ j ctx c, j < m → msg j ctx c (cache j ctx c) = P ctx j c
  /-- The cache after a challenge is the next stage's. -/
  step_eq : ∀ j ctx c x, j < m → step j ctx c (cache j ctx c) x = cache (j + 1) ctx (c.push x)

variable [∀ i, OracleInterface (O i)] {P : Polys F X O W d} {m : ℕ} (R : RoundCache P m)

/-- The cache at a stage's statement. -/
abbrev RoundCache.at {j : ℕ} (p : (Stmt X F j × ∀ i, O i) × W) : R.C j :=
  R.cache j (ctxOf p) p.1.1.2.1

/-- The cache at the statement between a round's message and its challenge. -/
abbrev RoundCache.atMid {j : ℕ} (p : (MidStmt X F j d × ∀ i, O i) × W) : R.C j :=
  R.cache j ((p.1.1.1.1, p.1.2), p.2) p.1.1.1.2.1

/-- The cached message of round `j`: the polynomial read off the cache, which stays. -/
def cachedSendPoly (j : ℕ) (hj : j < m) :
    Component.Cached (sendPoly P j) (R.at (j := j)) (R.atMid (j := j)) :=
  Component.Cached.sendChecked (msg := fun p c ↦ R.msg j (ctxOf p) p.1.1.2.1 c)
    (upd := fun _ c _ ↦ c) (fun p ↦ R.msg_eq j (ctxOf p) p.1.1.2.1 hj) fun _ ↦ rfl

variable [DecidableEq F] [SampleableType F] (wt : Weights F X)

/-- The cached challenge of round `j`: the cache updated by the challenge. -/
def cachedDrawChallenge (j : ℕ) (hj : j < m) :
    Component.Cached (drawChallenge (d := d) j wt) (R.atMid (j := j)) (R.at (j := j + 1)) :=
  Component.Cached.sample (upd := fun p c x ↦ R.step j ((p.1.1.1.1, p.1.2), p.2) p.1.1.1.2.1 c x)
    fun _ x ↦ R.step_eq j _ _ x hj

/-- The cached round `j`. -/
def cachedRound (j : ℕ) (hj : j < m) :
    Component.Cached (round P j wt) (R.at (j := j)) (R.at (j := j + 1)) :=
  (cachedSendPoly R j hj).append (cachedDrawChallenge R wt j hj)

/-- The cached prover of the `i` rounds from stage `j` to stage `m = j + i`: the cache of stage
`j` taken, that of stage `m` handed on. -/
def cachedRounds : (i j : ℕ) → (h : j + i = m) →
    Component.Cached (rounds P wt m i j h) (R.at (j := j)) (R.at (j := m))
  | 0, j, h => Component.Cached.passThrough (upd := fun _ c ↦ cast (congrArg R.C h) c)
    fun _ ↦ by
      obtain rfl : j = m := h
      rfl
  | i + 1, j, h =>
    (cachedRound R wt j (by omega)).append (cachedRounds i (j + 1) (by omega))

end SumcheckRound

end
end LeanerVM.Protocol
