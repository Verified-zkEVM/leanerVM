/-
  LeanVM.Guest.B1.Sig.SphincsSub

  A sub-tree and a coordinate of `verify_sig_lean_sphincs`'s forest are sound: the dispatches they
  take, read off the valuation, give the forest key's child leaf, the folds, the super-child and the
  running encoding and bound.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsFold
public import LeanVM.Guest.B1.Sig.Codeword

/-!
# A sub-tree and a coordinate, sound

* `subFk`, `subE`, `subAdr`, `subFd`, `sSubtree_eq`: the parts of `sSubtree`;
* `subA`, `subT`: the child and the codeword index its two dispatches take (`logG`);
* `sSubtree_sound` (`SubFacts`): the key's address, the child leaf, the encoding and the bound
  updated, the reached level-2 node;
* `coordAdr`, `coordFd`, `sCoord_eq`, `coordS`, `sCoord_sound` (`CoordFacts`): the leaf's address,
  the two sub-trees, the super-child, the reached level-3 node and the bound.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-! ## A sub-tree -/

/-- The 256 forest keys of sub-tree `j` of coordinate `c` at base `b`. -/
def subFk (c j b : Nat) : List (List Stmt) × Nat × V × V := fkArms (2 * c + j) (.n (b + 11)) (b + 12)

/-- The encoding's update: the statements, the updated cell and the next base. -/
def subE (c j : Nat) (enc : Option V) (b : Nat) : List Stmt × V × Nat :=
  if 2 * c + j + 1 = 16 then ([addS (.n 17) (enc.getD (.n 0)) (subFk c j b).2.2.2], .n 17, (subFk c j b).2.1)
  else match enc with
    | none => ([], (subFk c j b).2.2.2, (subFk c j b).2.1)
    | some en => ([addS (.n (subFk c j b).2.1) en (subFk c j b).2.2.2], .n (subFk c j b).2.1,
        (subFk c j b).2.1 + 1)

/-- A sub-tree node's address cell: `sub_tws[2 a + l]`. -/
def subAdr : Nat → Nat → Sum V Nat := fun a l => .inl (sSubTws (2 * a + l))

/-- The 8 folds of sub-tree `j` of coordinate `c` at base `b`. -/
def subFd (c j : Nat) (enc : Option V) (b : Nat) : List (List Stmt) × Nat × (V × V × V) :=
  foldArms (.n (b + 11)) subAdr 3 (subFk c j b).2.2.1 (.n (b + 1))
    (fun a => word (j * 2 ^ 39 + a * 2 ^ 40) 0 0) (fun a => cbMul a (58 + 3 * (2 * c + j)))
    (subE c j enc b).2.2

theorem sSubtree_eq (c j : Nat) (leafAt : V) (enc : Option V) (bound : V) (b : Nat) :
    sSubtree c j leafAt enc bound b =
      ([hintW "sp_keys" [.n b, .n (b + 1)]] ++ rangeS (.n b) g7W (b + 2) ++
        [hintW "sp_words" [.n (b + 6)]] ++ rangeS (.n (b + 6)) g255W (b + 7) ++
        [addS (.n (b + 11)) leafAt (.n (b + 1)), .match_ (.n (b + 6)) (subFk c j b).1] ++
        (subE c j enc b).1 ++
        [.match_ (.n b) (subFd c j enc b).1,
          addS (.n (subFd c j enc b).2.1) bound (subFd c j enc b).2.2.2.2],
        (subFd c j enc b).2.1 + 1, (subE c j enc b).2.1, .n (subFd c j enc b).2.1,
        ((subFd c j enc b).2.2.1, (subFd c j enc b).2.2.2.1)) := rfl

/-- The child index sub-tree's fold dispatch takes. -/
noncomputable def subA (σ : Val) (b : Nat) : Nat := logG (σ (.n b)) 8

/-- The codeword index sub-tree's forest key dispatch takes. -/
noncomputable def subT (σ : Val) (b : Nat) : Nat := logG (σ (.n (b + 6))) 256

/-- The running encoding's value: `0` before the first sub-tree. -/
def encVal (σ : Val) : Option V → E
  | none => 0
  | some en => σ en

/-- **What a sub-tree establishes.** -/
structure SubFacts (σ : Val) (c j : Nat) (leafAt : V) (enc : Option V) (bound : V) (b : Nat) :
    Prop where
  a_lt : subA σ b < 8
  t_lt : subT σ b < 256
  keyOK : σ (.n (b + 11)) = σ leafAt + word (j * 2 ^ 39 + subA σ b * 2 ^ 40) 0 0
  leaf : σ (subFk c j b).2.2.1 =
    (hcell (σ sPP :: (σ (.n (b + 11)) + word (tw 16) 0 0) :: (List.range 6).map fun i =>
      fChain (σ sPP) (σ (.n (b + 11))) i (4 - spCode (subT σ b) i)
        (σ (.n (fkCB (subT σ b) (.n (b + 11)) 0 (fkAB (2 * c + j) (.n (b + 11)) (b + 12) (subT σ b)) i)))
        (spCode (subT σ b) i))).1
  encOK : σ (subE c j enc b).2.1 = encVal σ enc + fkWeight (subT σ b) (2 * c + j)
  node : σ (if subA σ b / 2 ^ 2 = 0 then (subFd c j enc b).2.2.1 else (subFd c j enc b).2.2.2.1) =
    mFold (σ sPP) (flAdr σ (.n (b + 11)) (subAdr (subA σ b))) (subA σ b).testBit
      (fun l' => σ (.n (flBase (subAdr (subA σ b)) 0 l'
        (foAB (.n (b + 11)) subAdr 3 (subFk c j b).2.2.1 (.n (b + 1))
          (fun a => word (j * 2 ^ 39 + a * 2 ^ 40) 0 0) (fun a => cbMul a (58 + 3 * (2 * c + j)))
          (subE c j enc b).2.2 (subA σ b)))))
      2 0 (σ (subFk c j b).2.2.1)
  boundOK : σ (.n (subFd c j enc b).2.1) = σ bound + cbMul (subA σ b) (58 + 3 * (2 * c + j))

theorem subE_atoms (c j : Nat) (enc : Option V) (b : Nat) : atomsOnly (subE c j enc b).1 = true := by
  unfold subE
  split
  · rfl
  · split <;> rfl

theorem logG_of_match {x : E} {j n : Nat} (hj : j < n) (hn : n ≤ 2 ^ 64 - 1) (hx : x = ofK (gpow j)) :
    logG x n = j := logG_eq hj hn hx

/-- **A sub-tree, sound.** -/
theorem sSubtree_sound (hp : PadOK σ sPad) (htws : TwsOK σ) {c j : Nat} {leafAt : V}
    {enc : Option V} {bound : V} {b : Nat} (henc : 2 * c + j + 1 = 16 → enc ≠ none)
    {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ ((sSubtree c j leafAt enc bound b).1 ++ rest) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧ SubFacts σ c j leafAt enc bound b := by
  rw [sSubtree_eq] at h
  simp only [List.append_assoc, List.cons_append] at h
  have h1 : Stmt.HoldsList C rd σ (([hintW "sp_keys" [.n b, .n (b + 1)]] ++ rangeS (.n b) g7W (b + 2) ++
      [hintW "sp_words" [.n (b + 6)]] ++ rangeS (.n (b + 6)) g255W (b + 7) ++
      [addS (.n (b + 11)) leafAt (.n (b + 1))]) ++
      (.match_ (.n (b + 6)) (subFk c j b).1 :: ((subE c j enc b).1 ++
        (.match_ (.n b) (subFd c j enc b).1 ::
          addS (.n (subFd c j enc b).2.1) bound (subFd c j enc b).2.2.2.2 :: rest)))) next kret := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append,
      rangeS] using h
  have s1 := holdsList_split_atoms rfl h1
  have hkey : σ (.n (b + 11)) = σ leafAt + σ (.n (b + 1)) :=
    (atomsHold_of_holdsList rfl s1.1).atom (a := .add (.n (b + 11)) leafAt (.n (b + 1)))
      (by simp [addS])
  obtain ⟨t, ht, hxt, hfk, s2⟩ := holdsList_match (fkArms_atoms _ _ _) s1.2
  have ht256 : t < 256 := by rwa [fkArms_length] at ht
  have hT : subT σ b = t := logG_of_match ht256 (by norm_num) hxt
  obtain ⟨hleaf, hw⟩ := fkArms_sound hp htws ht hfk
  have s3 := holdsList_split_atoms (subE_atoms c j enc b) s2
  obtain ⟨a, ha, hxa, hfd, s4⟩ := holdsList_match (foldArms_atoms _ _ _ _ _ _ _ _) s3.2
  have ha8 : a < 8 := by
    rw [foldArms_length] at ha
    simpa using ha
  have hA : subA σ b = a := logG_of_match ha8 (by norm_num) hxa
  obtain ⟨hnode, hmark, hwt⟩ := foldArms_sound hp ha hfd
  have hb : σ (.n (subFd c j enc b).2.1) = σ bound + σ (subFd c j enc b).2.2.2.2 := s4.1
  refine ⟨s4.2, ⟨by rw [hA]; exact ha8, by rw [hT]; exact ht256, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hkey, hA, hmark]
  · rw [hT]
    exact hleaf
  · have he := (atomsHold_of_holdsList (subE_atoms c j enc b) s3.1)
    rw [hT, ← hw]
    unfold subE at he ⊢
    by_cases h16 : 2 * c + j + 1 = 16
    · simp only [h16, ↓reduceIte] at he ⊢
      have := he.atom (a := .add (.n 17) (enc.getD (.n 0)) (subFk c j b).2.2.2) (by simp [addS])
      rw [this]
      cases enc with
      | none => exact absurd rfl (henc h16)
      | some en => rfl
    · simp only [h16, ↓reduceIte] at he ⊢
      cases enc with
      | none => simp only [encVal, zero_add]; rfl
      | some en =>
          have := he.atom (a := .add (.n (subFk c j b).2.1) en (subFk c j b).2.2.2) (by simp [addS])
          exact this
  · rw [hA]
    exact hnode
  · rw [hb, hA]
    exact congrArg (σ bound + ·) hwt

/-! ## A coordinate -/

/-- A top-tree node's address constant: `topNode`'s fields at level `l` above super-child `s`. -/
def coordAdr : Nat → Nat → Sum V Nat :=
  fun s l => .inr (s * 2 ^ 35 ^^^ (tw 19 + (l + 1) * (8 * hiMul) + s / 2 ^ (l + 1) * (64 * hiMul)))

/-- The 16 folds of coordinate `c`, after its sub-trees end at `f`. -/
def coordFd (c b f : Nat) : List (List Stmt) × Nat × (V × V × V) :=
  foldArms (.n (b + 6)) coordAdr 4 (.n (f + 5)) (.n (b + 1))
    (fun s => word (c * hiMul + s * 2 ^ 35) 0 0) (fun s => cbMul s (26 + 4 * c)) (f + 18)

/-- Coordinate `c`'s sub-tree `0`. -/
def coordS0 (c : Nat) (enc : Option V) (bound : V) (b : Nat) :=
  sSubtree c 0 (.n (b + 6)) enc bound (b + 10)

/-- Coordinate `c`'s sub-tree `1`. -/
def coordS1 (c : Nat) (enc : Option V) (bound : V) (b : Nat) :=
  sSubtree c 1 (.n (b + 6)) (some (coordS0 c enc bound b).2.2.1) (coordS0 c enc bound b).2.2.2.1
    (coordS0 c enc bound b).2.1

theorem sCoord_eq (c : Nat) (enc : Option V) (bound : V) (b : Nat) :
    sCoord c enc bound b =
      ([hintW "sp_leaves" [.n b, .n (b + 1)]] ++ rangeS (.n b) g15W (b + 2) ++
        [addS (.n (b + 6)) (sNode 0) (.n (b + 1)), copyS (.n (b + 7)) sPP, cst (b + 8) (word (tw 18) 0 0),
          addS (.n (b + 9)) (.n (b + 6)) (.n (b + 8))] ++
        (coordS0 c enc bound b).1 ++ (coordS1 c enc bound b).1 ++
        [copyS (.n (coordS1 c enc bound b).2.1) (coordS1 c enc bound b).2.2.2.2.1,
          copyS (.n ((coordS1 c enc bound b).2.1 + 1)) (coordS1 c enc bound b).2.2.2.2.2,
          cst ((coordS1 c enc bound b).2.1 + 2) (word 1 0 0),
          cst ((coordS1 c enc bound b).2.1 + 3) (word 0 0 0),
          cst ((coordS1 c enc bound b).2.1 + 4) (word (2 ^ 63) 0 0),
          kecS [.n (b + 7), .n (b + 9), (coordS0 c enc bound b).2.2.2.2.1,
            (coordS0 c enc bound b).2.2.2.2.2, .n (coordS1 c enc bound b).2.1,
            .n ((coordS1 c enc bound b).2.1 + 1), .n ((coordS1 c enc bound b).2.1 + 2),
            .n ((coordS1 c enc bound b).2.1 + 3), .n ((coordS1 c enc bound b).2.1 + 4),
            .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)]
            (runV ((coordS1 c enc bound b).2.1 + 5) 13) false false,
          .match_ (.n b) (coordFd c b (coordS1 c enc bound b).2.1).1,
          addS (if c + 1 = 8 then .n 18 else .n (coordFd c b (coordS1 c enc bound b).2.1).2.1)
            (coordS1 c enc bound b).2.2.2.1 (coordFd c b (coordS1 c enc bound b).2.1).2.2.2.2],
        if c + 1 = 8 then (coordFd c b (coordS1 c enc bound b).2.1).2.1
          else (coordFd c b (coordS1 c enc bound b).2.1).2.1 + 1,
        (coordS1 c enc bound b).2.2.1,
        if c + 1 = 8 then .n 18 else .n (coordFd c b (coordS1 c enc bound b).2.1).2.1,
        ((coordFd c b (coordS1 c enc bound b).2.1).2.2.1,
          (coordFd c b (coordS1 c enc bound b).2.1).2.2.2.1)) := rfl

/-- The super-child coordinate `c`'s top fold dispatch takes. -/
noncomputable def coordS (σ : Val) (b : Nat) : Nat := logG (σ (.n b)) 16

/-- **What a coordinate establishes**, besides its sub-trees'. -/
structure CoordFacts (σ : Val) (c : Nat) (enc : Option V) (bound : V) (b : Nat) : Prop where
  s_lt : coordS σ b < 16
  leafOK : σ (.n (b + 6)) = σ (sNode 0) + word (c * hiMul + coordS σ b * 2 ^ 35) 0 0
  sub0 : SubFacts σ c 0 (.n (b + 6)) enc bound (b + 10)
  sub1 : SubFacts σ c 1 (.n (b + 6)) (some (coordS0 c enc bound b).2.2.1)
    (coordS0 c enc bound b).2.2.2.1 (coordS0 c enc bound b).2.1
  super : σ (.n ((coordS1 c enc bound b).2.1 + 5)) =
    (hcell [σ sPP, σ (.n (b + 6)) + word (tw 18) 0 0,
      σ (coordS0 c enc bound b).2.2.2.2.1, σ (coordS0 c enc bound b).2.2.2.2.2,
      σ (coordS1 c enc bound b).2.2.2.2.1, σ (coordS1 c enc bound b).2.2.2.2.2]).1
  node : σ (if coordS σ b / 2 ^ 3 = 0 then (coordFd c b (coordS1 c enc bound b).2.1).2.2.1
      else (coordFd c b (coordS1 c enc bound b).2.1).2.2.2.1) =
    mFold (σ sPP) (flAdr σ (.n (b + 6)) (coordAdr (coordS σ b))) (coordS σ b).testBit
      (fun l' => σ (.n (flBase (coordAdr (coordS σ b)) 0 l'
        (foAB (.n (b + 6)) coordAdr 4 (.n ((coordS1 c enc bound b).2.1 + 5)) (.n (b + 1))
          (fun s => word (c * hiMul + s * 2 ^ 35) 0 0) (fun s => cbMul s (26 + 4 * c))
          ((coordS1 c enc bound b).2.1 + 18) (coordS σ b)))))
      3 0 (σ (.n ((coordS1 c enc bound b).2.1 + 5)))
  boundOK : σ (sCoord c enc bound b).2.2.2.1 =
    σ (coordS1 c enc bound b).2.2.2.1 + cbMul (coordS σ b) (26 + 4 * c)

/-- **A coordinate, sound.** -/
theorem sCoord_sound (hp : PadOK σ sPad) (htws : TwsOK σ) {c : Nat} {enc : Option V}
    {bound : V} {b : Nat} {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ ((sCoord c enc bound b).1 ++ rest) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧ CoordFacts σ c enc bound b := by
  rw [sCoord_eq] at h
  have h1 : Stmt.HoldsList C rd σ (([hintW "sp_leaves" [.n b, .n (b + 1)]] ++ rangeS (.n b) g15W (b + 2) ++
      [addS (.n (b + 6)) (sNode 0) (.n (b + 1)), copyS (.n (b + 7)) sPP, cst (b + 8) (word (tw 18) 0 0),
        addS (.n (b + 9)) (.n (b + 6)) (.n (b + 8))]) ++
      ((coordS0 c enc bound b).1 ++ ((coordS1 c enc bound b).1 ++
      ([copyS (.n (coordS1 c enc bound b).2.1) (coordS1 c enc bound b).2.2.2.2.1,
          copyS (.n ((coordS1 c enc bound b).2.1 + 1)) (coordS1 c enc bound b).2.2.2.2.2,
          cst ((coordS1 c enc bound b).2.1 + 2) (word 1 0 0),
          cst ((coordS1 c enc bound b).2.1 + 3) (word 0 0 0),
          cst ((coordS1 c enc bound b).2.1 + 4) (word (2 ^ 63) 0 0),
          kecS [.n (b + 7), .n (b + 9), (coordS0 c enc bound b).2.2.2.2.1,
            (coordS0 c enc bound b).2.2.2.2.2, .n (coordS1 c enc bound b).2.1,
            .n ((coordS1 c enc bound b).2.1 + 1), .n ((coordS1 c enc bound b).2.1 + 2),
            .n ((coordS1 c enc bound b).2.1 + 3), .n ((coordS1 c enc bound b).2.1 + 4),
            .n (sPad + 1), .n (sPad + 2), .n (sPad + 3), .n (sPad + 4)]
            (runV ((coordS1 c enc bound b).2.1 + 5) 13) false false] ++
      (.match_ (.n b) (coordFd c b (coordS1 c enc bound b).2.1).1 ::
        addS (if c + 1 = 8 then .n 18 else .n (coordFd c b (coordS1 c enc bound b).2.1).2.1)
          (coordS1 c enc bound b).2.2.2.1 (coordFd c b (coordS1 c enc bound b).2.1).2.2.2.2 :: rest)))))
      next kret := by
    simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using h
  have s1 := holdsList_split_atoms rfl h1
  have a1 := atomsHold_of_holdsList rfl s1.1
  have hla : σ (.n (b + 6)) = σ (sNode 0) + σ (.n (b + 1)) :=
    a1.atom (a := .add (.n (b + 6)) (sNode 0) (.n (b + 1))) (by simp [addS])
  have hpp : σ (.n (b + 7)) = σ sPP := a1.atom (a := .copy (.n (b + 7)) sPP) (by simp [copyS])
  have h8 : σ (.n (b + 8)) = word (tw 18) 0 0 := a1.atom (a := .const (.n (b + 8)) _) (by simp [cst])
  have h9 : σ (.n (b + 9)) = σ (.n (b + 6)) + σ (.n (b + 8)) :=
    a1.atom (a := .add (.n (b + 9)) (.n (b + 6)) (.n (b + 8))) (by simp [addS])
  obtain ⟨s2, f0⟩ := sSubtree_sound hp htws (c := c) (j := 0) (fun h => by omega) s1.2
  obtain ⟨s3, f1⟩ := sSubtree_sound hp htws (c := c) (j := 1) (fun _ => by simp) s2
  have s4 := holdsList_split_atoms rfl s3
  have a4 := atomsHold_of_holdsList rfl s4.1
  set f := (coordS1 c enc bound b).2.1 with hf
  have c0 : σ (.n f) = σ (coordS1 c enc bound b).2.2.2.2.1 :=
    a4.atom (a := .copy (.n f) (coordS1 c enc bound b).2.2.2.2.1) (by simp [copyS])
  have c1 : σ (.n (f + 1)) = σ (coordS1 c enc bound b).2.2.2.2.2 :=
    a4.atom (a := .copy (.n (f + 1)) (coordS1 c enc bound b).2.2.2.2.2) (by simp [copyS])
  have c2 : σ (.n (f + 2)) = word 1 0 0 := a4.atom (a := .const (.n (f + 2)) _) (by simp [cst])
  have c3 : σ (.n (f + 3)) = word 0 0 0 := a4.atom (a := .const (.n (f + 3)) _) (by simp [cst])
  have c4 : σ (.n (f + 4)) = word (2 ^ 63) 0 0 := a4.atom (a := .const (.n (f + 4)) _) (by simp [cst])
  rw [word_zero] at c3
  have hk := kec96_sound (o := f + 5) (m0 := .n (b + 7)) (m1 := .n (b + 9))
    (m2 := (coordS0 c enc bound b).2.2.2.2.1) (m3 := (coordS0 c enc bound b).2.2.2.2.2)
    (m4 := .n f) (m5 := .n (f + 1)) hp (a4.sub fun x hx => by
    simp only [List.mem_singleton] at hx
    subst hx
    simp) c2 c3 c4
  obtain ⟨s, hs, hxs, hfd, s5⟩ := holdsList_match (foldArms_atoms _ _ _ _ _ _ _ _) s4.2
  have hs16 : s < 16 := by
    rw [foldArms_length] at hs
    simpa using hs
  have hS : coordS σ b = s := logG_of_match hs16 (by norm_num) hxs
  obtain ⟨hnode, hmark, hwt⟩ := foldArms_sound hp hs hfd
  have hbd := s5.1
  refine ⟨s5.2, ⟨by rw [hS]; exact hs16, ?_, f0, f1, ?_, ?_, ?_⟩⟩
  · rw [hla, hS, hmark]
  · have hk1 := congrArg Prod.fst hk
    simp only at hk1
    rw [hk1, hpp, h9, h8, c0, c1]
  · rw [hS]
    exact hnode
  · simp only [Atom.Holds] at hbd
    rw [sCoord_eq]
    simp only
    rw [hbd, hS]
    exact congrArg (σ (coordS1 c enc bound b).2.2.2.1 + ·) hwt

end
end LeanVM.Guest.B1.Sig
