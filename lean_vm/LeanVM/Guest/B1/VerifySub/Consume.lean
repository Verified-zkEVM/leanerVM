/-
  LeanVM.Guest.B1.VerifySub.Consume

  How many stream words the phases of the deferring verifier read: a fixed number, given the
  sizes, for GKR, the tables, Flock and the stacked opening.
-/

module

public import LeanVM.Guest.B1.VerifySub.Run

/-!
# The phases' stream lengths

`Reads Q n p`: every successful run of `p` reads exactly `n` stream words (a `read` or a `grind`
one, a `commit` two) and returns a value satisfying `Q`. `Reads.run`: a successful run of such a
program consumes exactly `n` words of its stream; so does a `RunsTo` (`RunsTo.length_eq`) or a
`RunsWith` (`RunsWith.length_eq`).

The phases `verify_sub` hands to callees read a number of words fixed by the sizes:

* `gkrLen depth` for `gkrPhase depth` (`reads_gkrPhase`);
* `tablesLen layout` for `tablesSeg` on the claimed values (`reads_tablesSeg`), six tables;
* `flockLen logN` for `verifyFlock` on the claimed values (`reads_verifyFlock`);
* `whirLen μ r` for `whirOpen μ r` (`reads_whirOpen`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Programs reading a fixed number of words -/

/-- Every successful run of `p` reads exactly `n` stream words and returns a value satisfying
`Q`. Irreducible: elaborating a `Reads` of a long program would otherwise unfold it. -/
@[irreducible] def Reads {α : Type} (Q : α → Prop) : ℕ → Prog α → Prop
  | n, .ret a => n = 0 ∧ Q a
  | _, .fail => True
  | n + 1, .read k => ∀ x, Reads Q n (k x)
  | n, .sample k => ∀ x, Reads Q n (k x)
  | n + 1, .grind _ k => Reads Q n k
  | n + 2, .commit _ _ k => Reads Q n k
  | n, .query _ _ k => ∀ r, Reads Q n (k r)
  | 0, .read _ => False
  | 0, .grind _ _ => False
  | 0, .commit _ _ _ => False
  | 1, .commit _ _ _ => False

variable {α β : Type}

unseal Reads in
theorem Reads.mono {Q Q' : α → Prop} (hQ : ∀ a, Q a → Q' a) :
    ∀ {n : ℕ} {p : Prog α}, Reads Q n p → Reads Q' n p
  | _, .ret a, h => ⟨h.1, hQ a h.2⟩
  | _, .fail, _ => trivial
  | _ + 1, .read _, h => fun x => Reads.mono hQ (h x)
  | 0, .read _, h => h.elim
  | _, .sample _, h => fun x => Reads.mono hQ (h x)
  | _ + 1, .grind _ k, h => Reads.mono hQ (p := k) h
  | 0, .grind _ _, h => h.elim
  | _ + 2, .commit _ _ k, h => Reads.mono hQ (p := k) h
  | 0, .commit _ _ _, h => h.elim
  | 1, .commit _ _ _, h => h.elim
  | _, .query _ _ _, h => fun r => Reads.mono hQ (h r)

unseal Reads in
theorem Reads.bind {Q : α → Prop} {R : β → Prop} {m : ℕ} {f : α → Prog β}
    (hf : ∀ a, Q a → Reads R m (f a)) :
    ∀ {n : ℕ} {p : Prog α}, Reads Q n p → Reads R (n + m) (p.bind f)
  | _, .ret a, h => by
    obtain ⟨rfl, hq⟩ := h
    simpa [Prog.bind] using hf a hq
  | _, .fail, _ => trivial
  | n + 1, .read k, h => by
    rw [show n + 1 + m = n + m + 1 by omega]
    exact fun x => Reads.bind hf (p := k x) (h x)
  | 0, .read _, h => h.elim
  | _, .sample k, h => fun x => Reads.bind hf (p := k x) (h x)
  | n + 1, .grind _ k, h => by
    rw [show n + 1 + m = n + m + 1 by omega]
    exact Reads.bind hf (p := k) h
  | 0, .grind _ _, h => h.elim
  | n + 2, .commit _ _ k, h => by
    rw [show n + 2 + m = n + m + 2 by omega]
    exact Reads.bind hf (p := k) h
  | 0, .commit _ _ _, h => h.elim
  | 1, .commit _ _ _, h => h.elim
  | _, .query _ _ k, h => fun r => Reads.bind hf (p := k r) (h r)

/-- `Reads.bind` at a given total. -/
theorem Reads.bind' {Q : α → Prop} {R : β → Prop} {n m k : ℕ} {p : Prog α} {f : α → Prog β}
    (hp : Reads Q n p) (hf : ∀ a, Q a → Reads R m (f a)) (hk : n + m = k) :
    Reads R k (p >>= f) := hk ▸ Reads.bind hf hp

/-- One step of a program: the first part's reads, then the rest's, the total left last. -/
macro "rbind" : tactic => `(tactic| refine Reads.bind' ?_ (fun _ _ => ?_) ?_)

unseal Reads in
theorem reads_ret {Q : α → Prop} {a : α} (h : Q a) : Reads Q 0 (Prog.ret a) := ⟨rfl, h⟩

unseal Reads in
theorem reads_pure {Q : α → Prop} {a : α} (h : Q a) : Reads Q 0 (pure a : Prog α) := ⟨rfl, h⟩

unseal Reads in
theorem reads_fail {Q : α → Prop} (n : ℕ) : Reads Q n (Prog.fail : Prog α) := by
  cases n <;> trivial

unseal Reads in
/-- A successful run of a program reading `n` words consumes `n` words of its stream. -/
theorem Reads.run {Q : α → Prop} :
    ∀ {n : ℕ} {p : Prog α}, Reads Q n p → ∀ {s : St} {a : α} {s' : St}, runId p s = some (a, s') →
      Q a ∧ ∃ ys : List E, ys.length = n ∧ s.stream = ys ++ s'.stream
  | _, .ret a, h, s, b, s', hr => by
    obtain ⟨rfl, hq⟩ := h
    have hr' : some (a, s) = some (b, s') := hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr'
    obtain ⟨rfl, rfl⟩ := hr'
    exact ⟨hq, [], rfl, rfl⟩
  | _, .fail, _, _, _, _, hr => by cases hr
  | _ + 1, .read _, _, ⟨_, [], _, _⟩, _, _, hr => by cases hr
  | _ + 1, .read k, h, ⟨cv, x :: xs, os, roots⟩, _, _, hr => by
    obtain ⟨hq, ys, hl, he⟩ := Reads.run (h x) (s := ⟨obsCv cv x, xs, os, roots⟩) hr
    exact ⟨hq, x :: ys, by simp [hl], congrArg (x :: ·) he⟩
  | 0, .read _, h, _, _, _, _ => h.elim
  | _, .sample k, h, ⟨cv, xs, os, roots⟩, _, _, hr =>
    Reads.run (h _) (s := ⟨sqCv cv, xs, os, roots⟩) hr
  | _ + 1, .grind _ _, _, ⟨_, [], _, _⟩, _, _, hr => by cases hr
  | _ + 1, .grind b k, h, ⟨cv, x :: xs, os, roots⟩, a, s', hr => by
    have hr' : (if powOk b x (blake2sBytes (digestBytes (blake2sBytes (digestBytes cv ++ blockOf 0 3)) ++
        blockOf x 4)) then runId k ⟨blake2sBytes (digestBytes cv ++ blockOf x 4), xs, os, roots⟩
        else none) = some (a, s') := hr
    split at hr'
    · obtain ⟨hq, ys, hl, he⟩ := Reads.run (p := k) h hr'
      exact ⟨hq, x :: ys, by simp [hl], congrArg (x :: ·) he⟩
    · cases hr'
  | 0, .grind _ _, h, _, _, _, _ => h.elim
  | _ + 2, .commit _ _ _, _, ⟨_, [], _, _⟩, _, _, hr => by cases hr
  | _ + 2, .commit _ _ _, _, ⟨_, [_], _, _⟩, _, _, hr => by cases hr
  | _ + 2, .commit hh ww k, h, ⟨cv, x0 :: x1 :: xs, os, roots⟩, a, s', hr => by
    simp only [runId, Compile.run] at hr
    split at hr
    · obtain ⟨hq, ys, hl, he⟩ := Reads.run (p := k) h hr
      exact ⟨hq, x0 :: x1 :: ys, by simp [hl], congrArg (fun l => x0 :: x1 :: l) he⟩
    · cases hr
  | 0, .commit _ _ _, h, _, _, _, _ => h.elim
  | 1, .commit _ _ _, h, _, _, _, _ => h.elim
  | _, .query _ ps k, h, ⟨cv, xs, os, roots⟩, a, s', hr => by
    simp only [runId, Compile.run] at hr
    split at hr
    · cases hr
    · rename_i root hh ww _
      cases hoa : openAll (m := Id) blake2sBytes root hh ww ps os with
      | none => rw [hoa] at hr; cases hr
      | some r =>
        obtain ⟨rows, rest⟩ := r
        rw [hoa] at hr
        exact Reads.run (h rows) (s := ⟨cv, xs, rest, roots⟩) hr

/-- A run reading exactly `xs` of a program reading `n` words: `xs` has `n` words. -/
theorem RunsTo.length_eq {Q : α → Prop} {n : ℕ} {p : Prog α} {cv cv' : Digest} {xs : List E}
    {a : α} (h : RunsTo p cv xs a cv') (hp : Reads Q n p) : xs.length = n ∧ Q a := by
  obtain ⟨hq, ys, hl, he⟩ := hp.run (h [] [] [])
  simp only [List.append_nil] at he
  exact ⟨by rw [he, hl], hq⟩

/-- A run reading exactly `xs` and openings of a program reading `n` words: `xs` has `n`
words. -/
theorem RunsWith.length_eq {Q : α → Prop} {n : ℕ} {p : Prog α} {cv cv' : Digest} {xs : List E}
    {os : List Opening} {roots roots' : List (Digest × ℕ × ℕ)} {a : α}
    (h : RunsWith p cv xs os roots a cv' roots') (hp : Reads Q n p) : xs.length = n ∧ Q a := by
  obtain ⟨hq, ys, hl, he⟩ := hp.run (h [] [])
  simp only [List.append_nil] at he
  exact ⟨by rw [he, hl], hq⟩

/-! ## The operations -/

unseal Reads in
theorem reads_readE : Reads (fun _ => True) 1 Prog.readE := fun _ => ⟨rfl, trivial⟩

theorem reads_readN : ∀ n, Reads (fun l : List E => l.length = n) n (Prog.readN n)
  | 0 => reads_ret rfl
  | n + 1 => by
    show Reads _ (n + 1) (Prog.readE >>= fun x => Prog.readN n >>= fun xs => pure (x :: xs))
    exact Reads.bind' reads_readE (fun x _ => Reads.bind' (reads_readN n)
      (fun xs h => reads_pure (by simp [h])) rfl) (by omega)

unseal Reads in
theorem reads_sampleE : Reads (fun _ => True) 0 Prog.sampleE := fun _ => ⟨rfl, trivial⟩

theorem reads_sampleN : ∀ n, Reads (fun l : List E => l.length = n) 0 (Prog.sampleN n)
  | 0 => reads_ret rfl
  | n + 1 => by
    show Reads _ 0 (Prog.sampleE >>= fun x => Prog.sampleN n >>= fun xs => pure (x :: xs))
    exact Reads.bind' reads_sampleE (fun x _ => Reads.bind' (reads_sampleN n)
      (fun xs h => reads_pure (by simp [h])) rfl) rfl

unseal Reads in
theorem reads_require (c : Prop) [Decidable c] : Reads (fun _ => True) 0 (Prog.require c) := by
  unfold Prog.require
  split
  · exact ⟨rfl, trivial⟩
  · trivial

unseal Reads in
theorem reads_grindP (bits : ℕ) : Reads (fun _ => True) 1 (Prog.grindP bits) := ⟨rfl, trivial⟩

unseal Reads in
theorem reads_commitP (h w : ℕ) : Reads (fun _ => True) 2 (Prog.commitP h w) := ⟨rfl, trivial⟩

unseal Reads in
theorem reads_queryP (i : ℕ) (ps : List ℕ) : Reads (fun _ => True) 0 (Prog.queryP i ps) :=
  fun _ => ⟨rfl, trivial⟩

unseal Reads in
theorem reads_liftOption (o : Option α) : Reads (fun a => o = some a) 0 (Verifier.liftOption o) := by
  cases o with
  | none => trivial
  | some a => exact ⟨rfl, rfl⟩

/-! ## Sumchecks -/

theorem reads_sumcheckRoundPoly {count : ℕ} (hc : 2 ≤ count) (claim : E) (e : Option E) :
    Reads (fun l : List E => l.length = count) (count - 1) (sumcheckRoundPoly count claim e) := by
  cases e with
  | none =>
    unfold sumcheckRoundPoly
    refine Reads.bind' reads_readE (fun c _ => Reads.bind' (reads_readN (count - 2))
      (fun t ht => reads_pure (by simp [ht]; omega)) rfl) (by omega)
  | some ef =>
    unfold sumcheckRoundPoly
    exact Reads.bind' (reads_readN (count - 1)) (fun t ht => reads_pure (by simp [ht]; omega)) rfl

theorem reads_sumcheck {count : ℕ} (hc : 2 ≤ count) :
    ∀ (claim : E) (eqs : List (Option E)),
      Reads (fun r : List E × E => r.1.length = eqs.length) (eqs.length * (count - 1))
        (sumcheck claim count eqs)
  | claim, [] => by simp only [sumcheck, List.length_nil, Nat.zero_mul]; exact reads_pure rfl
  | claim, e :: eqs => by
    unfold sumcheck
    refine Reads.bind' (reads_sumcheckRoundPoly hc claim e) (fun msg _ =>
      Reads.bind' reads_sampleE (fun ch _ => Reads.bind' (reads_sumcheck hc _ eqs)
        (fun r hr => reads_pure (by simp [hr])) rfl) rfl) (by simp; ring)

/-! ## GKR -/

theorem reads_gkrStep (step : ℕ) (s : GkrState) :
    Reads (fun s' : GkrState => s'.point.length = step + s.point.length)
      (s.point.length * 2 ^ step + 3 * 2 ^ step) (gkrStep step s) := by
  unfold gkrStep
  have h2 : 2 ≤ 2 ^ step + 1 := by have := Nat.one_le_two_pow (n := step); omega
  refine Reads.bind' reads_sampleE (fun cb _ => ?_) (zero_add _)
  refine Reads.bind' (reads_sumcheck h2 _ _) (fun r hr => ?_) (m := 3 * 2 ^ step) (by simp)
  obtain ⟨x, claim⟩ := r
  simp only [List.length_map] at hr
  refine Reads.bind' (reads_readN _) (fun c0 _ => ?_) (m := 2 * 2 ^ step) (by ring)
  refine Reads.bind' (reads_readN _) (fun c1 _ => ?_) (m := 2 ^ step) (by ring)
  refine Reads.bind' (reads_readN _) (fun c2 _ => ?_) (m := 0) rfl
  refine Reads.bind' (reads_require _) (fun _ _ => ?_) (m := 0) rfl
  exact Reads.bind' (reads_sampleN step) (fun y hy => reads_pure (by simp [hy, hr])) rfl

/-- The words `gkrLayers n` reads from a point of `p` coordinates. -/
def gkrLayersLen : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, p => p * 2 ^ 1 + 3 * 2 ^ 1 + gkrLayersLen 0 (1 + p)
  | n + 2, p =>
    if n % 2 = 1 then p * 2 ^ 1 + 3 * 2 ^ 1 + gkrLayersLen (n + 1) (1 + p)
    else p * 2 ^ 2 + 3 * 2 ^ 2 + gkrLayersLen n (2 + p)

theorem reads_gkrLayers : ∀ (n : ℕ) (s : GkrState),
    Reads (fun s' : GkrState => s'.point.length = s.point.length + n)
      (gkrLayersLen n s.point.length) (gkrLayers n s)
  | 0, s => reads_pure (by simp)
  | 1, s => by
    show Reads _ _ (gkrStep 1 s >>= fun s => gkrLayers 0 s)
    refine Reads.bind' (reads_gkrStep 1 s) (fun s' hs' => ?_) rfl
    exact (reads_gkrLayers 0 s').mono fun a ha => by rw [ha, hs']; omega
  | n + 2, s => by
    by_cases hn : n % 2 = 1
    · have e : gkrLayers (n + 2) s = (gkrStep 1 s >>= fun s => gkrLayers (n + 1) s) := by
        simp [gkrLayers, hn]
      rw [e]; simp only [gkrLayersLen, hn, ↓reduceIte]
      refine Reads.bind' (reads_gkrStep 1 s) (fun s' hs' => ?_) rfl
      have := reads_gkrLayers (n + 1) s'
      rw [hs'] at this
      exact this.mono fun a ha => by rw [ha]; omega
    · have e : gkrLayers (n + 2) s = (gkrStep 2 s >>= fun s => gkrLayers n s) := by
        simp [gkrLayers, hn]
      rw [e]; simp only [gkrLayersLen, hn, ↓reduceIte]
      refine Reads.bind' (reads_gkrStep 2 s) (fun s' hs' => ?_) rfl
      have := reads_gkrLayers n s'
      rw [hs'] at this
      exact this.mono fun a ha => by rw [ha]; omega

/-- The words GKR reads at depth `depth`: the two roots, then the layers. -/
def gkrLen (depth : ℕ) : ℕ := 2 + gkrLayersLen depth 0

theorem reads_verifyGkrGrandProducts (depth : ℕ) :
    Reads (fun _ => True) (gkrLen depth) (verifyGkrGrandProducts depth) := by
  unfold verifyGkrGrandProducts gkrLen
  refine Reads.bind' reads_readE (fun sh _ => ?_) (m := 1 + gkrLayersLen depth 0) (by omega)
  refine Reads.bind' reads_readE (fun ct _ => ?_) (m := gkrLayersLen depth 0) (by omega)
  exact Reads.bind' (reads_gkrLayers depth _) (fun _ _ => reads_pure trivial) rfl

theorem reads_gkrPhase (depth : ℕ) : Reads (fun _ => True) (gkrLen depth) (gkrPhase depth) := by
  unfold gkrPhase
  exact Reads.bind' (reads_verifyGkrGrandProducts depth)
    (fun _ _ => Reads.bind' (reads_require _) (fun _ _ => reads_pure trivial) rfl) rfl

/-! ## The tables -/

theorem accumulateSide_length (forms : List (List Form)) (side : ℕ) (blocks : List BusBlock)
    (sideLayout : BusLayout) (ff sw : List E) (sb : E) (point : List E) (tv : E) :
    (accumulateSide forms side blocks sideLayout ff sw sb point tv).1.length = forms.length := by
  unfold accumulateSide
  simp only
  generalize List.zip _ blocks = l
  suffices h : ∀ (acc : List (List Form) × E),
      (l.foldl (fun (acc : List (List Form) × E) (x : E × BusBlock) =>
        (acc.1.modify x.2.owner fun row ↦ row.modify side fun f ↦
          f.addScaled (blockForm x.2 sw sb) x.1,
        acc.2 + x.1 * paddingWeight (point.take x.2.logRows) x.2.rows *
          (Form.evaluate (blockForm x.2 sw sb)
            (fun i => ((tables.getD x.2.owner default).padding).getD i 0) + 1))) acc).1.length =
        acc.1.length from h (forms, 0)
  induction l with
  | nil => intro acc; rfl
  | cons x l ih => intro acc; rw [List.foldl_cons, ih]; simp

theorem reads_busRest (c : FixedClaims) (layout : Layout) (alphas : List E) (beta : E)
    (point tv : List E) :
    Reads (fun b : BusResult => b.forms.length = tables.length) 5
      (busRest (.claimed c) layout alphas beta point tv) := by
  unfold busRest
  dsimp only
  refine Reads.bind' (reads_readN 3) (fun mem _ => ?_) (m := 2) rfl
  refine Reads.bind' reads_readE (fun mf _ => ?_) (m := 1) rfl
  refine Reads.bind' reads_readE (fun bf _ => ?_) (m := 0) rfl
  refine Reads.bind' (Reads.bind' (reads_require _) (fun _ _ => reads_pure (Q := fun _ : E => True) trivial) rfl)
    (fun bv _ => reads_pure ?_) rfl
  simp [accumulateSide_length]

theorem tableWeights_length (heights : List ℕ) (eqp point : List E) :
    (tableWeights heights eqp point).length = heights.length := by
  unfold tableWeights
  generalize point.zipIdx = l
  suffices h : ∀ w : List E, w.length = heights.length →
      (l.foldl (fun weights (x : E × ℕ) ↦ List.zipWith (fun weight height ↦ weight *
        if x.2 < height then 1 + eqp.getD x.2 0 + x.1 else x.1) weights heights) w).length =
        heights.length from h _ (by simp)
  induction l with
  | nil => intro w hw; exact hw
  | cons x l ih => intro w hw; rw [List.foldl_cons]; exact ih _ (by simp [hw])

theorem reads_tableTerms (cp fp point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E) (claims : List ColumnClaim),
      Reads (fun _ => True) ((rows.map fun r ↦ r.1.width).sum)
        (tableTerms cp fp point rows cursor final claims)
  | [], _, _, _ => reads_pure trivial
  | (t, h, f, w) :: rest, cursor, final, claims => by
    unfold tableTerms
    exact Reads.bind' (reads_readN t.width) (fun _ _ => reads_tableTerms cp fp point rest _ _ _)
      (by simp)

/-- The words the tables' phase reads at a layout of six tables: the bus's five, the table
sumcheck's rounds, every table's row. -/
def tablesLen (layout : Layout) : ℕ :=
  5 + (layout.tableLogHeights.foldl max 0 * (4 - 1) + (tables.map Table.width).sum)

theorem reads_tableSumcheck {heights : List ℕ} (hh : heights.length = tables.length)
    {forms : List (List Form)} (hf : forms.length = tables.length) (cp fp eqp : List E) (target : E) :
    Reads (fun _ => True) (heights.foldl max 0 * (4 - 1) + (tables.map Table.width).sum)
      (tableSumcheck heights forms cp fp eqp target) := by
  unfold tableSumcheck
  dsimp only
  refine Reads.bind' (reads_sumcheck (by omega) _ _) (fun r _ => ?_)
    (m := (tables.map Table.width).sum) (by simp)
  obtain ⟨ch, cl⟩ := r
  dsimp only
  refine Reads.bind' (reads_tableTerms cp fp _ _ 0 0 []) (fun r _ => ?_) (m := 0) ?_
  · obtain ⟨fin, cls⟩ := r
    exact Reads.bind' (reads_require _) (fun _ _ => reads_pure trivial) rfl
  · rw [Nat.add_zero]
    congr 1
    rw [show (fun r : Table × ℕ × List Form × E => r.1.width) = Table.width ∘ Prod.fst from rfl,
      ← List.map_map, List.map_fst_zip (by simp [hh, hf, tableWeights_length])]

theorem reads_tablePhase (layout : Layout) (hl : layout.tableLogHeights.length = tables.length)
    (bus : BusResult) (hb : bus.forms.length = tables.length) :
    Reads (fun _ => True) (layout.tableLogHeights.foldl max 0 * (4 - 1) + (tables.map Table.width).sum)
      (tablePhase layout bus) := by
  unfold tablePhase
  exact Reads.bind' reads_sampleE (fun _ _ => Reads.bind' (reads_tableSumcheck hl hb _ _ _ _)
    (fun _ _ => reads_pure trivial) rfl) (by simp)

theorem reads_publicInputPhase (layout : Layout) (pi : Digest) :
    Reads (fun _ => True) 0 (publicInputPhase layout pi) := by
  unfold publicInputPhase
  exact Reads.bind' reads_sampleE (fun _ _ => reads_pure trivial) rfl

theorem reads_tablesSeg (c : FixedClaims) {layout : Layout}
    (hl : layout.tableLogHeights.length = tables.length) (pi : Digest) (alphas : List E) (beta : E)
    (point tv : List E) :
    Reads (fun _ => True) (tablesLen layout) (tablesSeg (.claimed c) layout pi alphas beta point tv) := by
  unfold tablesSeg tablesLen
  exact Reads.bind' (reads_busRest c layout alphas beta point tv) (fun b hb =>
    Reads.bind' (reads_tablePhase layout hl b hb) (fun _ _ => Reads.bind' (reads_publicInputPhase _ _)
      (fun _ _ => reads_pure trivial) rfl) rfl) rfl

/-! ## Flock -/

theorem reads_verifyFlockZerocheck (logN : ℕ) :
    Reads (fun _ => True)
      (kBits + ((fixedChallenges.length + (logN - flockKSkip - fixedChallenges.length)) * (3 - 1) + 2))
      (verifyFlockZerocheck logN) := by
  unfold verifyFlockZerocheck
  refine Reads.bind' (reads_sampleN _) (fun sm hsm => ?_) (zero_add _)
  refine Reads.bind' (reads_readN kBits) (fun pc _ => ?_)
    (m := (fixedChallenges.length + (logN - flockKSkip - fixedChallenges.length)) * (3 - 1) + 2) rfl
  refine Reads.bind' reads_sampleE (fun z _ => ?_) (zero_add _)
  dsimp only
  refine Reads.bind' (reads_sumcheck (by norm_num) _ _) (fun r _ => ?_) (m := 2) (by simp [hsm])
  obtain ⟨chi, running⟩ := r
  exact Reads.bind' reads_readE (fun _ _ => Reads.bind' reads_readE (fun _ _ => reads_pure trivial)
    rfl) rfl

theorem reads_verifyFlockLincheck (c : FixedClaims) (zc : ZerocheckResult) :
    Reads (fun _ => True) (flockNumLincheckRounds * (3 - 1) + kBits)
      (verifyFlockLincheck (.claimed c) zc) := by
  unfold verifyFlockLincheck
  refine Reads.bind' reads_sampleE (fun al _ => ?_) (zero_add _)
  dsimp only
  refine Reads.bind' (reads_sumcheck (by norm_num) _ _) (fun r _ => ?_) (m := kBits) (by simp)
  obtain ⟨rc, rlc⟩ := r
  dsimp only
  refine Reads.bind' (reads_readN kBits) (fun sl _ => ?_) (m := 0) rfl
  refine Reads.bind' (Reads.bind' (reads_require _)
    (fun _ _ => reads_pure (Q := fun _ : E => True) trivial) rfl) (fun mv _ => ?_) (m := 0) rfl
  exact Reads.bind' (reads_require _) (fun _ _ => reads_pure trivial) rfl

/-- The words Flock reads on `logN` variables: the coset's `kBits`, the zerocheck's rounds and
two closing values, the lincheck's rounds and the `kBits` slices. -/
def flockLen (logN : ℕ) : ℕ :=
  kBits + ((fixedChallenges.length + (logN - flockKSkip - fixedChallenges.length)) * (3 - 1) + 2) +
    (flockNumLincheckRounds * (3 - 1) + kBits)

theorem reads_verifyFlock (c : FixedClaims) (logN : ℕ) :
    Reads (fun _ => True) (flockLen logN) (verifyFlock (.claimed c) logN) := by
  unfold verifyFlock flockLen
  exact Reads.bind' (reads_verifyFlockZerocheck logN) (fun zc _ => reads_verifyFlockLincheck c zc) rfl

end
end LeanVM.Guest.B1.VerifySub
