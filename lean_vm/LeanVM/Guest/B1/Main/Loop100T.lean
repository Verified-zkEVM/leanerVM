/-
  LeanVM.Guest.B1.Main.Loop100T

  `__loop100` complete under any semantics by trees loading their `cover_da_root` callees' reads.
-/

module

public import LeanVM.Guest.B1.Main.LoopsAtS
public import LeanVM.Guest.B1.Comp.Digest.SmallLoads

/-!
# `__loop100` in tree form

`loop100S_completeAt` with the callees' trees kept (`completeAtS_loopBT`): iteration `c` calls
`cover_da_root` at the slot `sl c`, whose tree loads the mark at `dcov·g^(sl c)` and the root's
four cells at `roots·g^(4·sl c)` (`CoverLoadsQ`, `CovA`); the loop's tree loads them all
(`L100A … m 0`):

* `loadsAll_covA`: `CoverLoadsQ` as a set of load equations;
* `loop100_events`: the iteration's path;
* `loop100S_iterBST`: one iteration, from the next one's;
* `loop100S_completeAtBST`: the loop.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 (LowDef CompleteAtBST CompleteRelBST LoadsAll LoadsAt LoadsCells Returns kidsBound)
open LeanVM.Guest.B1.Digest (KidR CallsR CoverLoadsQ)

@[expose] public section

variable {S : BlakeSem} {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`cover_da_root`'s load equations at the slot `i`**: the mark at `cover·g^i`, the root's four
cells at `roots·g^(4i)`. -/
def CovA (roots cover mark : E) (i : ℕ) (rt : List E) (q : K × E) : Prop :=
  q = ((cover * gen ^ i).limb 0 * Parameters.gpow 0, mark) ∨
    ∃ k < 4, q = ((roots * gen ^ (4 * i)).limb 0 * Parameters.gpow k, rt.getD k 0)

theorem loadsAll_covA {t : Memory.Tree} {roots cover nslots mark r0 r1 r2 r3 : E} {i fp : ℕ}
    {rd : Reader} (h : CoverLoadsQ i [roots, cover, nslots, mark] [r0, r1, r2, r3] fp rd t) :
    LoadsAll (CovA roots cover mark i [r0, r1, r2, r3]) t := by
  obtain ⟨h1, h2⟩ := h
  rintro q (rfl | ⟨k, hk, rfl⟩)
  · exact h1
  · have := h2 k (by simpa using hk)
    interval_cases k <;> simpa [LoadsAt] using this

/-- **The load equations of `__loop100`'s iterations `j, …, m - 1`.** -/
def L100A (roots dcov base nsub : E) (sl : ℕ → ℕ) (rt : ℕ → List E) (m j : ℕ) (q : K × E) : Prop :=
  ∃ c, j ≤ c ∧ c < m ∧ CovA roots dcov (base * nsub * gen ^ c) (sl c) (rt c) q

/-- `__loop100`'s path: its calls, no addresses nor allocations, its four loads. -/
theorem loop100_events (σ : Val) :
    calls (loop100Pre.flatMap (slEvs σ)) =
      [⟨"cover_da_root", [.n 3, .n 4, .n 5, .n 12], [.n 13, .n 14, .n 15, .n 16], true⟩,
        ⟨"__loop100", [.n 21, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], [], decide (σ (.n 19) ≠ 0)⟩] ∧
    addrs (loop100Pre.flatMap (slEvs σ)) = [] ∧ allocs σ (loop100Pre.flatMap (slEvs σ)) = [] ∧
    allocDsts (loop100Pre.flatMap (slEvs σ)) = [] ∧
    loadAddrs σ (loop100Pre.flatMap (slEvs σ)) =
      ([(.n 10, 0), (.n 10, 1), (.n 10, 2), (.n 10, 3)] : List (V × ℕ)).map
        fun q => (σ q.1).limb 0 * Parameters.gpow q.2 := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := loop100_parts
  obtain ⟨h1, h2, h3, h4⟩ := straight_parts σ _ p1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h4, p4]; rfl
  · rw [h3, p3]
  · rw [h2, p2]; rfl
  · rw [h1, p2]; rfl
  · rw [LeanVM.Guest.B1.loadAddrs_straight σ _ p1, p5]

/-- **One iteration of `__loop100`, complete under any semantics by a tree loading its slots'
marks and roots** (`loop100S_completeAt`'s step), from the next one's. -/
theorem loop100S_iterBST {κ Bc : ℕ}
    (H : ∀ i, CompleteRelBST S fs cert κ "cover_da_root" (CoverPreAt i) Bc (CoverLoadsQ i))
    {m cdab : ℕ} {roots dcov dslots base nsub : E} (hm : m < 2 ^ 16) (Lin : Layout)
    (rt : ℕ → List E) (hlen : ∀ c < m, (rt c).length = 4) (sl : ℕ → ℕ)
    (hcov : ∀ c < m, ∀ rd, LowDef κ rd → MemL rd Lin →
      CoverPreAt (sl c) rd [roots, dcov, dslots, base * nsub * gen ^ c] (rt c))
    (hcda : ∀ c < m, ∀ k < 4, CellL Lin (cdab + 4 * c + k) ((rt c).getD k 0)) {j : ℕ} (hj : j < m)
    (hnext : j + 1 < m → CompleteAtBST S fs cert κ "__loop100" Lin
      [gen ^ (j + 1), gen ^ m, ofK (Parameters.gpow cdab), roots, dcov, dslots, base, nsub] (Returns [])
      ((m - (j + 1)) * (fs "__loop100" + Bc) + fs "__loop100")
      fun _ _ t => LoadsAll (L100A roots dcov base nsub sl rt m (j + 1)) t) :
    CompleteAtBST S fs cert κ "__loop100" Lin
      [gen ^ j, gen ^ m, ofK (Parameters.gpow cdab), roots, dcov, dslots, base, nsub] (Returns [])
      ((m - j) * (fs "__loop100" + Bc) + fs "__loop100")
      fun _ _ t => LoadsAll (L100A roots dcov base nsub sl rt m j) t := by
  obtain ⟨r0, r1, r2, r3, hr⟩ : ∃ a b c d, rt j = [a, b, c, d] := by
    have := hlen j hj
    match rt j, this with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  have hmore : decide (gen ^ j * gen + gen ^ m ≠ 0) = true → j + 1 < m := fun ht => by
    have : gen ^ j * gen + gen ^ m ≠ 0 := by simpa using ht
    rw [← pow_succ] at this
    by_contra h
    exact this (by rw [show m = j + 1 by omega]; exact e_add_self _)
  refine LeanVM.Guest.B1.completeAtS_loopBT find_loop100 loop100_isLoop κ Lin _ []
    [⟨"cover_da_root", true, [roots, dcov, dslots, base * nsub * gen ^ j], Lin, rt j⟩]
    ⟨"__loop100", decide (gen ^ j * gen + gen ^ m ≠ 0),
      [gen ^ (j + 1), gen ^ m, ofK (Parameters.gpow cdab), roots, dcov, dslots, base, nsub], Lin, []⟩
    (fun _ => Bc) ((m - (j + 1)) * (fs "__loop100" + Bc) + fs "__loop100")
    (fun _ => CovA roots dcov (base * nsub * gen ^ j) (sl j) (rt j))
    (L100A roots dcov base nsub sl rt m (j + 1)) ?_ ?_ _ ?_ ?_
    (L100A roots dcov base nsub sl rt m j) ?_
  · intro k hk _
    simp only [List.mem_singleton] at hk
    subst hk
    refine (H (sl j) _ _ Lin fun rd hl hL => hcov j hj rd hl hL).qmono fun fp rd t h => ?_
    rw [hr] at h ⊢
    exact loadsAll_covA h
  · intro ht
    exact hnext (hmore ht)
  · simp only [kidsBound, KidR.kid, List.map_cons, List.map_nil, ite_true, List.sum_cons,
      List.sum_nil]
    have : fs "__loop100" ≤ (m - (j + 1)) * (fs "__loop100" + Bc) + fs "__loop100" := by omega
    rw [max_eq_left this, show m - j = m - (j + 1) + 1 by omega]
    ring_nf
    omega
  · intro k hk _ i hi
    simp only [List.mem_append, List.mem_singleton] at hk
    rcases hk with rfl | rfl <;> exact hi
  intro rd hl hL
  refine ⟨fun k hk => by
    simp only [List.mem_append, List.mem_singleton] at hk; rcases hk with rfl | rfl <;> exact hL, ?_⟩
  set σ := loop100Val (gen ^ j) (gen ^ m) (ofK (Parameters.gpow cdab)) roots dcov dslots base nsub r0 r1 r2 r3
    with hσ
  obtain ⟨p1, -, -, -, -⟩ := loop100_parts
  have hcj := hcda j hj
  rw [hr] at hcj
  have hrd : ReadsAt rd (ofK (Parameters.gpow cdab) * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)))
      [r0, r1, r2, r3] := by
    rw [gen_pow_four, ofK_gpow_mul_gen]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    have := (hcj k hk).load hL
    interval_cases k <;> simpa using this
  have hK : IsInK (gen ^ j * gen + gen ^ m) :=
    isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1)) (gen_pow_isInK _)
  have hh := loop100S_holds (S := S) (C := fun _ _ _ => True) (rd := rd) (N := gen ^ m)
    (roots := roots) (dcov := dcov) (dslots := dslots) (base := base) (nsub := nsub) trivial hrd hK
    (fun _ => trivial)
  have hw : walk σ (Fn.body Data.core573) = .ret (loop100Pre.flatMap (slEvs σ)) [] := by
    rw [core573_split]; exact walk_straight σ [] _ p1
  have hsat := walkB_sat (P := coreProgram) _ (coreProgram_wf _ (List.mem_of_find?_eq_some find_loop100)) hh
  rw [hw] at hsat
  obtain ⟨e1, e2, e3, e4, e5⟩ := loop100_events σ
  refine ⟨σ, _, [], ?_, hw, rfl, fun e he => (hsat.1 e he).1, ?_, e2, e3, e4, fun A hA => ?_,
    fun q ⟨c, hc1, hc2, hq⟩ => ?_⟩
  · simp only [show Fn.params Data.core573 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]
      from rfl, List.map_cons, List.map_nil, hσ, loop100Val]; b1_look
  · rw [e1]
    refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, ?_, fun _ => ⟨?_, rfl⟩, trivial⟩
    · simp only [List.map_cons, List.map_nil, hσ, loop100Val]; b1_look
    · rw [hr]; simp only [List.map_cons, List.map_nil, hσ, loop100Val]; b1_look
    · simp only [hσ, loop100Val]; b1_look
    · simp only [List.map_cons, List.map_nil, hσ, loop100Val]; b1_look
      rw [gen_pow_mul_gen]
  · rw [e5] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    have e10 : ∀ k, ofK (Parameters.gpow cdab) * (gen ^ j * gen ^ j * (gen ^ j * gen ^ j)) * gen ^ k =
        ofK (Parameters.gpow (cdab + 4 * j + k)) := fun k => by
      rw [gen_pow_four, ofK_gpow_mul_gen, ofK_gpow_mul_gen]
    have hreg : ∀ k < 4, RegionL Lin (cdab + 4 * j + k) := fun k hk => (hcj k hk).region
    rcases hA with rfl | rfl | rfl | rfl <;> simp only [hσ, loop100Val] <;> b1_look
    · exact ⟨_, by rw [← mul_one (ofK _ * _), ← pow_zero gen, e10, addr_ofK], hreg 0 (by omega)⟩
    · exact ⟨_, by rw [← mul_one (ofK _ * _), ← pow_zero gen, e10, addr_ofK], hreg 1 (by omega)⟩
    · exact ⟨_, by rw [← mul_one (ofK _ * _), ← pow_zero gen, e10, addr_ofK], hreg 2 (by omega)⟩
    · exact ⟨_, by rw [← mul_one (ofK _ * _), ← pow_zero gen, e10, addr_ofK], hreg 3 (by omega)⟩
  · rcases Nat.eq_or_lt_of_le hc1 with rfl | hlt
    · exact Or.inr (Or.inl ⟨_, List.mem_singleton_self _, rfl, hq⟩)
    · refine Or.inr (Or.inr ⟨decide_eq_true fun h0 => ?_, c, by omega, hc2, hq⟩)
      rw [← pow_succ] at h0
      have := gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp h0)
      omega

/-- **`__loop100`, complete under any semantics by a tree loading every iteration's slot mark and
root** (`loop100S_completeAt`). -/
theorem loop100S_completeAtBST {κ Bc : ℕ}
    (H : ∀ i, CompleteRelBST S fs cert κ "cover_da_root" (CoverPreAt i) Bc (CoverLoadsQ i))
    {m cdab : ℕ} {roots dcov dslots base nsub : E} (hm : m < 2 ^ 16) (hm0 : 0 < m) (Lin : Layout)
    (rt : ℕ → List E) (hlen : ∀ c < m, (rt c).length = 4) (sl : ℕ → ℕ)
    (hcov : ∀ c < m, ∀ rd, LowDef κ rd → MemL rd Lin →
      CoverPreAt (sl c) rd [roots, dcov, dslots, base * nsub * gen ^ c] (rt c))
    (hcda : ∀ c < m, ∀ k < 4, CellL Lin (cdab + 4 * c + k) ((rt c).getD k 0)) :
    CompleteAtBST S fs cert κ "__loop100" Lin
      [1, gen ^ m, ofK (Parameters.gpow cdab), roots, dcov, dslots, base, nsub] (Returns [])
      (m * (fs "__loop100" + Bc) + fs "__loop100")
      fun _ _ t => LoadsAll (L100A roots dcov base nsub sl rt m 0) t := by
  suffices h : ∀ d j, j + d + 1 = m → CompleteAtBST S fs cert κ "__loop100" Lin
      [gen ^ j, gen ^ m, ofK (Parameters.gpow cdab), roots, dcov, dslots, base, nsub] (Returns [])
      ((m - j) * (fs "__loop100" + Bc) + fs "__loop100")
      (fun _ _ t => LoadsAll (L100A roots dcov base nsub sl rt m j) t) by
    have := h (m - 1) 0 (by omega)
    rwa [pow_zero, Nat.sub_zero] at this
  intro d
  induction d with
  | zero =>
    exact fun j hj => loop100S_iterBST H hm Lin rt hlen sl hcov hcda (by omega)
      (fun h => absurd h (by omega))
  | succ d ih =>
    exact fun j hj => loop100S_iterBST H hm Lin rt hlen sl hcov hcda (by omega)
      (fun _ => ih (j + 1) (by omega))


/-- **What `__loop100`'s tree loads, at its call words**: every iteration's slot mark and root, for
some slots and roots. -/
def Loop100Q : List E → ℕ → Reader → Memory.Tree → Prop
  | [_, N, _, roots, dcov, _, base, nsub], _, _, t =>
      ∃ (m : ℕ) (sl : ℕ → ℕ) (rt : ℕ → List E), N = gen ^ m ∧
        LoadsAll (L100A roots dcov base nsub sl rt m 0) t
  | _, _, _, _ => True

/-- `CompleteAtBST` within weights bounding every valid tree (`CompleteAtB.toWS` with a
predicate). -/
theorem CompleteAtBST.toWST_valid {Θ : Type} {w : Θ → String → ℕ} {κ : ℕ} {f : String}
    {Lin : Layout} {args : List E} {Out : List E → Layout → Prop} {B : ℕ} {Bw : Θ → ℕ}
    {Q : ℕ → Reader → Memory.Tree → Prop} (h : CompleteAtBST S fs cert κ f Lin args Out B Q)
    (hw : ∀ θ (rd : Reader) (t : Memory.Tree) (rets : List E), t.name = f →
      t.ValidB S coreProgram rd args rets → t.BufsOk coreProgram → t.weight (w θ) ≤ Bw θ) :
    LeanVM.Guest.B1.CompleteAtWST S fs cert w κ f Lin args Out B Bw Q := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, hq, hn', hv, hb, hp, ht, hl', hd'⟩ := hr rd hl hm
    ⟨t, hq, hn', hv, hb, hp, ht, hl', hd', fun θ => hw θ rd t _ hn' hv hb⟩⟩

end
end LeanVM.Guest.B1.Main
