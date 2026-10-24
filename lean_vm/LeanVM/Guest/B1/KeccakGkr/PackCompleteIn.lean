/-
  LeanVM.Guest.B1.KeccakGkr.PackCompleteIn

  The pack rounds' loop helpers, completely and with their loads placed.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.PackComplete
public import LeanVM.Guest.B1.KeccakGkr.RoundCompleteIn

/-!
# The pack rounds' loop, its loads placed

Each iteration at `x` loads the record `rec·x` (the offsets `roundRecOffs`), the coordinates at
`pp·x²`, the challenges' slots at `pt·x²` and four stream words at the record's cursor
(`PackRegions`). With those words in a region `R` at every counter, the loop's relation loads from
`R` (`packLoop_relIn`): one tree per iteration (`Memory.relIn_of_walk`), its only callee the next
iteration.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The words an iteration at `x` loads lie in `R`. -/
def PackRegions (R : ℕ → Prop) (rd : Reader) (rec pp pt x : E) : Prop :=
  (∀ k ∈ roundRecOffs, InR R (rec * x) k) ∧ InR R (pp * x ^ 2) 0 ∧ InR R (pp * x ^ 2) 1 ∧
    InR R (pt * x ^ 2) 0 ∧ InR R (pt * x ^ 2) 1 ∧
    ∀ cur, LoadHolds rd (rec * x) 80 cur → ∀ k < 4, InR R cur k

theorem pack_atoms : packPre.all isAtom = true := by decide +kernel

theorem pack_straight (name : String) :
    (packPre ++ [Stmt.callIf (.n 130) name [.n 132, .n 1, .n 2, .n 3, .n 4]]).all Stmt.straight = true := by
  rw [List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨by decide +kernel, rfl⟩

theorem pack_loads (name : String) :
    (packPre ++ [Stmt.callIf (.n 130) name [.n 132, .n 1, .n 2, .n 3, .n 4]]).filterMap Stmt.loadS =
      [(.n 5, 0), (.n 5, 16), (.n 5, 32), (.n 5, 48), (.n 5, 64), (.n 5, 80), (.n 5, 96),
        (.n 5, 112), (.n 7, 0), (.n 14, 0), (.n 14, 1), (.n 8, 0), (.n 7, 1), (.n 14, 2),
        (.n 14, 3), (.n 8, 1), (.n 5, 1), (.n 5, 17), (.n 5, 33), (.n 5, 49), (.n 5, 65),
        (.n 5, 81), (.n 5, 97), (.n 5, 113)] := by
  rw [List.filterMap_append]
  have : packPre.filterMap Stmt.loadS = [(.n 5, 0), (.n 5, 16), (.n 5, 32), (.n 5, 48),
      (.n 5, 64), (.n 5, 80), (.n 5, 96), (.n 5, 112), (.n 7, 0), (.n 14, 0), (.n 14, 1), (.n 8, 0),
      (.n 7, 1), (.n 14, 2), (.n 14, 3), (.n 8, 1), (.n 5, 1), (.n 5, 17), (.n 5, 33), (.n 5, 49),
      (.n 5, 65), (.n 5, 81), (.n 5, 97), (.n 5, 113)] := by decide +kernel
  rw [this]; rfl

theorem pack_calls (name : String) :
    (packPre ++ [Stmt.callIf (.n 130) name [.n 132, .n 1, .n 2, .n 3, .n 4]]).filterMap Stmt.callS =
      [(some (.n 130), name, [.n 132, .n 1, .n 2, .n 3, .n 4], [])] := by
  rw [List.filterMap_append]
  have : packPre.filterMap Stmt.callS = [] := by decide +kernel
  rw [this]; rfl

/-- **One iteration on its loads' region**, the next one (if any) given. -/
theorem packLoop_relIn_step {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = packLoopT name) (hpar : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    {rd : Reader} {R : ℕ → Prop} {rec pp pt : E} {m k : ℕ} (hk : k < m)
    (hs : PackStep rd rec pp pt (gen ^ k)) (hR : PackRegions R rd rec pp pt (gen ^ k))
    (hnext : k + 1 < m → coreProgram.RelIn rd R name [gen ^ (k + 1), gen ^ m, rec, pp, pt] []) :
    coreProgram.RelIn rd R name [gen ^ k, gen ^ m, rec, pp, pt] [] := by
  obtain ⟨σ, hp, hblk, h5, h7, h8, h14, h130, h132⟩ := packBlock_complete (N := gen ^ m) hs
  obtain ⟨hrec, hpp0, hpp1, hpt0, hpt1, hcur⟩ := hR
  have hcur' := hcur _ h14
  have hw : walk σ fn.body = .ret ((packPre ++ [Stmt.callIf (.n 130) name
      [.n 132, .n 1, .n 2, .n 3, .n 4]]).flatMap (slEvs σ)) [] := by
    rw [hb, packLoopT_split, show packPre ++ [Stmt.callIf (.n 130) name
      [.n 132, .n 1, .n 2, .n 3, .n 4], .ret []] = (packPre ++ [Stmt.callIf (.n 130) name
      [.n 132, .n 1, .n 2, .n 3, .n 4]]) ++ [.ret []] by simp]
    exact walk_straight σ [] _ (pack_straight name)
  refine relIn_of_walk coreProgram_wf hf (by rw [hpar]; exact hp) hw rfl
    (fun e he ↦ ?_) (fun A hA ↦ ?_) (fun c hc ht ↦ ?_)
  · rw [List.flatMap_append, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨s, hs', hes⟩ := List.mem_flatMap.1 he
      have hat := List.all_eq_true.1 pack_atoms s hs'
      cases s with
      | atom a =>
        simp only [slEvs, List.mem_singleton] at hes
        subst hes
        exact (hblk _ hs').1
      | _ => simp [isAtom] at hat
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, slEvs,
        List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · show IsInK (σ (.n 130))
        rw [h130, ← pow_succ]
        exact Digest.gen_pow_add_isInK _ _
      · split <;> trivial
  · rw [loadAddrs_straight σ _ (pack_straight name), pack_loads] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    rw [h5, h7, h8] at hA
    have hr : ∀ j ∈ roundRecOffs, InR R (rec * gen ^ k) j := hrec
    simp only [roundRecOffs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hr
    obtain ⟨r0, r16, r32, r48, r64, r80, r96, r112, r1, r17, r33, r49, r65, r81, r97, r113⟩ := hr
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r0
    · exact r16
    · exact r32
    · exact r48
    · exact r64
    · exact r80
    · exact r96
    · exact r112
    · exact hpp0
    · exact hcur' 0 (by norm_num)
    · exact hcur' 1 (by norm_num)
    · exact hpt0
    · exact hpp1
    · exact hcur' 2 (by norm_num)
    · exact hcur' 3 (by norm_num)
    · exact hpt1
    · exact r1
    · exact r17
    · exact r33
    · exact r49
    · exact r65
    · exact r81
    · exact r97
    · exact r113
  · rw [(straight_parts σ _ (pack_straight name)).2.2.2, pack_calls] at hc
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
    subst hc
    simp only [mkCall, decide_eq_true_eq] at ht
    simp only [List.cons.injEq, and_true] at hp
    obtain ⟨-, h1, h2, h3, h4⟩ := hp
    have hk1 : k + 1 < m := by
      by_contra hge
      apply ht
      rw [h130, ← pow_succ, show k + 1 = m by omega]
      exact e_add_eq_zero_iff.mpr rfl
    show coreProgram.RelIn rd R name [σ (.n 132), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] []
    rw [h132, h1, h2, h3, h4, ← pow_succ]
    exact hnext hk1

/-- **The loop runs on its loads' region**, from every counter `g^k`, `k < m`. -/
theorem packLoop_relIn_of {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = packLoopT name) (hpar : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    {rd : Reader} {R : ℕ → Prop} {rec pp pt : E} {m : ℕ}
    (hs : ∀ j < m, PackStep rd rec pp pt (gen ^ j))
    (hR : ∀ j < m, PackRegions R rd rec pp pt (gen ^ j)) :
    ∀ k < m, coreProgram.RelIn rd R name [gen ^ k, gen ^ m, rec, pp, pt] [] := by
  have key : ∀ t k, k + 1 + t = m →
      coreProgram.RelIn rd R name [gen ^ k, gen ^ m, rec, pp, pt] [] := by
    intro t
    induction t with
    | zero =>
      intro k hk
      exact packLoop_relIn_step hf hb hpar (by omega) (hs k (by omega)) (hR k (by omega))
        (fun h ↦ absurd h (by omega))
    | succ t ih =>
      intro k hk
      exact packLoop_relIn_step hf hb hpar (by omega) (hs k (by omega)) (hR k (by omega))
        (fun _ ↦ ih (k + 1) (by omega))
  intro k hk
  exact key (m - k - 1) k (by omega)

theorem packLoop_relIn_guard {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = packLoopT name) (hpar : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    {rd : Reader} {R : ℕ → Prop} {rec pp pt : E} {m : ℕ}
    (hs : ∀ j < m, PackStep rd rec pp pt (gen ^ j))
    (hR : ∀ j < m, PackRegions R rd rec pp pt (gen ^ j)) :
    IsInK (1 + gen ^ m) ∧
      (1 + gen ^ m ≠ 0 → coreProgram.RelIn rd R name [1, gen ^ m, rec, pp, pt] []) := by
  refine ⟨by rw [← pow_zero gen]; exact Digest.gen_pow_add_isInK _ _, fun hne ↦ ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact absurd (e_add_eq_zero_iff.mpr (pow_zero gen).symm) hne
  · have := packLoop_relIn_of hf hb hpar hs hR 0 hm0
    rwa [pow_zero] at this

/-- **The pack rounds' loop is complete, its loads placed**: an honest iteration at every `g^j`,
`j < m`, its words in `R`, gives the guard and the loop run of `keccak_layer`'s call loading from
`R`. -/
theorem packLoop_relIn (first odd : ℕ) {rd : Reader} {R : ℕ → Prop} {rec pp pt : E} {m : ℕ}
    (hs : ∀ j < m, PackStep rd rec pp pt (gen ^ j))
    (hR : ∀ j < m, PackRegions R rd rec pp pt (gen ^ j)) :
    IsInK (1 + gen ^ m) ∧ (1 + gen ^ m ≠ 0 →
      coreProgram.RelIn rd R (packLoopName first odd) [1, gen ^ m, rec, pp, pt] []) := by
  unfold packLoopName
  split
  · exact packLoop_relIn_guard find_packLoop30 packLoop_body30 rfl hs hR
  · exact packLoop_relIn_guard find_packLoop31 packLoop_body31 rfl hs hR
  · exact packLoop_relIn_guard find_packLoop32 packLoop_body32 rfl hs hR
  · exact packLoop_relIn_guard find_packLoop33 packLoop_body33 rfl hs hR

end
end LeanVM.Guest.B1.VerifySub
