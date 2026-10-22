/-
  LeanerVM.Protocol.Whir.Decode

  List decoding of level 0 of WHIR's code: the decoder interface specified by the list relation,
  the brute-force decoder, the exact path a codeword takes, and the codewords near a `K`-valued
  word are `K`-valued.
-/

module

public import LeanerVM.Protocol.Whir.Lanes
public import LeanerVM.Protocol.ToCompPoly.LinearSolve
public import Mathlib.Data.List.Sublists

/-!
# List decoding

Category B: Annex B, `def:listbinding` (the commitment binds the list of interleaved codewords
within the threshold of the committed word) at leanVM pin
`a386121f84292f6fa663aaa3e570c15bc0240ea2`.

A *list decoder* at threshold `a` (`ListDecoder κ R a ℓ`) returns, for a lane word `F`, a list
without repetition of exactly the interleaved codewords of `2 ^ ℓ` lanes within the threshold of
`F` (`Cl κ R a ℓ F`, the list relation of `LeanerVM.Protocol.Whir.Lanes`). The specification is
the list relation itself, so a decoder meets WHIR's list relation by its field `mem_iff` and
nothing else is to be trusted of it.

* `candidateAt`: the messages whose encodings take the word's values at `2 ^ κ` distinct
  positions, lane by lane, by one Gaussian elimination (`gaussSolve`) of the encoder's matrix over
  `K` (`encodeMatrix`) with every lane as a right-hand side. Two codewords that agree on `2 ^ κ`
  positions are equal (`encode_eq_of_agree`), so the matrix is injective and the messages are
  found (`candidateAt_of_agree`).
* `ListDecoder.bruteForce`: interpolate on every set of `2 ^ κ` positions and keep
  the candidates within the threshold. Correct for every threshold `a ≥ 2 ^ κ`: a codeword within
  the threshold agrees with the word on a set of `2 ^ κ` positions, where it is the candidate.
  Its cost is the number of such sets, so it runs on toy words only.
* `exactFast`: the path an honest word takes. It interpolates on the first `2 ^ κ` positions and
  returns the candidate when its encoding is the whole word. When it succeeds, the list is that
  one candidate (`exactFast_eq`), for every decoder and every threshold with
  `2 ^ κ ≤ a ≤ 2 ^ (κ + R)`: a codeword within the threshold of a codeword agrees with it on
  `a ≥ 2 ^ κ` positions, so it is that codeword. `ListDecoder.exactFirst` tries it before another
  decoder, and at exact agreement it is a decoder on its own (`ListDecoder.exact`). It costs one
  interpolation, not the deployed inverse transform.
* `isInK_of_cl`: every codeword within the threshold of a `K`-valued word is `K`-valued: on
  `2 ^ κ` positions of agreement it is the interpolant of `K` values, which interpolation over
  `K` already finds.
-/

namespace LeanerVM.Protocol

open LeanerVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

namespace Whir

/-! ## Interpolation -/

section Interpolation

variable {S : Type} [Field S] (φ : K →+* S) (κ R : ℕ)

/-- The encoder's matrix at the positions `T`: row `i` holds the column weight of the position
`T i`, so that the row times a message is the message's encoding there. -/
def encodeMatrix {N : ℕ} (T : Fin N → Fin (2 ^ (κ + R))) : Fin N → Fin (2 ^ κ) → S :=
  fun i u ↦ ∏ k : Fin κ, if u.val.testBit k then φ (normW k (domainPt (T i))) else 1

/-- A row of the matrix times a message is the message's encoding at the row's position. -/
theorem sum_encodeMatrix {N : ℕ} (T : Fin N → Fin (2 ^ (κ + R)))
    (m : CMlPolynomialEval S κ) (i : Fin N) :
    ∑ u, encodeMatrix φ κ R T i u * m[u] = encode φ κ R m (T i) :=
  (encode_eq_sum φ κ R m (T i)).symm

variable {φ κ R}

/-- On `2 ^ κ` distinct positions the encoder's matrix is injective, when `κ + R ≤ 64` and `φ`
is injective: two messages whose encodings agree there are equal. -/
theorem encodeMatrix_injective (hφ : Function.Injective φ) (hb : κ + R ≤ 64)
    {T : Fin (2 ^ κ) → Fin (2 ^ (κ + R))} (hT : Function.Injective T) (x : Fin (2 ^ κ) → S)
    (hx : ∀ i, ∑ j, encodeMatrix φ κ R T i j * x j = 0) : x = 0 := by
  have hm := encode_eq_of_agree φ hb hφ (m := (Vector.ofFn x : CMlPolynomialEval S κ))
    (m' := (Vector.replicate (2 ^ κ) 0 : CMlPolynomialEval S κ)) (Finset.univ.map ⟨T, hT⟩)
    (by simp) fun v hv ↦ by
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hv
      rw [← sum_encodeMatrix, ← sum_encodeMatrix]
      simpa [Fin.getElem_fin] using hx i
  funext j
  have := congrArg (fun v : Vector S (2 ^ κ) ↦ v[j]) hm
  simpa [Fin.getElem_fin] using this

/-- Over `E`, the encoder's matrix is the image of the matrix over `K`. -/
theorem encodeMatrix_algebraMap {N : ℕ} (T : Fin N → Fin (2 ^ (κ + R))) (i : Fin N)
    (u : Fin (2 ^ κ)) :
    encodeMatrix (algebraMap K E) κ R T i u =
      algebraMap K E (encodeMatrix (RingHom.id K) κ R T i u) := by
  simp only [encodeMatrix, map_prod, apply_ite (algebraMap K E), map_one, RingHom.id_apply]

/-- A message over `E` encodes at `T i` to the row of the matrix over `K` acting on it. -/
theorem encode_eq_sum_smul {N : ℕ} (T : Fin N → Fin (2 ^ (κ + R))) (m : CMlPolynomialEval E κ)
    (i : Fin N) :
    encode (algebraMap K E) κ R m (T i) = ∑ u, encodeMatrix (RingHom.id K) κ R T i u • m[u] := by
  rw [← sum_encodeMatrix]
  simp only [encodeMatrix_algebraMap, Algebra.smul_def]

end Interpolation

/-! ## Positions of agreement -/

/-- The family of a list of `2 ^ κ` positions. -/
def listPositions {κ b : ℕ} (l : List (Fin (2 ^ b))) (h : l.length = 2 ^ κ) :
    Fin (2 ^ κ) → Fin (2 ^ b) :=
  fun i ↦ l[i.val]'(by rw [h]; exact i.isLt)

/-- A list of distinct positions has an injective family. -/
theorem listPositions_injective {κ b : ℕ} {l : List (Fin (2 ^ b))} (h : l.length = 2 ^ κ)
    (hl : l.Nodup) : Function.Injective (listPositions (κ := κ) l h) := fun _ _ hij ↦
  Fin.ext ((List.Nodup.getElem_inj_iff hl).mp hij)

/-- The positions at which the codeword of `V` agrees with `F`. -/
def agreeSet (κ R m : ℕ) (F : LW (κ + R)) (V : Msgs m κ) : Finset (Fin (2 ^ (κ + R))) :=
  Finset.univ.filter fun y ↦ ∀ u : Fin (2 ^ m), encode (algebraMap K E) κ R (V u) y = F y u

/-- The first `2 ^ κ` positions of agreement, in increasing order. -/
def agreeList (κ R m : ℕ) (F : LW (κ + R)) (V : Msgs m κ) : List (Fin (2 ^ (κ + R))) :=
  ((List.finRange (2 ^ (κ + R))).filter fun y ↦ y ∈ agreeSet κ R m F V).take (2 ^ κ)

/-- A codeword within a threshold of at least `2 ^ κ` agrees with the word on a sublist of
`2 ^ κ` distinct positions. -/
theorem agreeList_spec {κ R a m : ℕ} (hdist : 2 ^ κ ≤ a) {F : LW (κ + R)} {V : Msgs m κ}
    (hV : Cl κ R a m F V) :
    List.Sublist (agreeList κ R m F V) (List.finRange (2 ^ (κ + R))) ∧
      (agreeList κ R m F V).length = 2 ^ κ ∧ (agreeList κ R m F V).Nodup ∧
      ∀ y ∈ agreeList κ R m F V, y ∈ agreeSet κ R m F V := by
  set l₀ := (List.finRange (2 ^ (κ + R))).filter fun y ↦ y ∈ agreeSet κ R m F V
  have hsub : List.Sublist (agreeList κ R m F V) (List.finRange (2 ^ (κ + R))) :=
    (List.take_sublist _ _).trans List.filter_sublist
  have hnd : l₀.Nodup := (List.nodup_finRange _).sublist List.filter_sublist
  have hcard : l₀.length = (agreeSet κ R m F V).card := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext y
    simp [l₀]
  refine ⟨hsub, ?_, (List.nodup_finRange _).sublist hsub, fun y hy ↦ ?_⟩
  · have hA : a ≤ (agreeSet κ R m F V).card := hV
    rw [agreeList, List.length_take]
    change min (2 ^ κ) l₀.length = 2 ^ κ
    rw [hcard]
    omega
  · have := List.mem_of_mem_take hy
    simpa using (List.mem_filter.mp this).2

/-! ## The list decoder -/

/-- A list decoder at the threshold `a`: for every lane word, a list without repetition of exactly
the interleaved codewords of `2 ^ ℓ` lanes within the threshold of the word. -/
structure ListDecoder (κ R a ℓ : ℕ) where
  /-- The list. -/
  decode : LW (κ + R) → List (Msgs ℓ κ)
  /-- It is the list relation. -/
  mem_iff : ∀ F V, V ∈ decode F ↔ Cl κ R a ℓ F V
  /-- It has no repetition. -/
  nodup : ∀ F, (decode F).Nodup

variable {κ R a ℓ : ℕ}

/-- A decoder's list is at most as long as the list bound: it has no repetition and holds only
codewords within the threshold. -/
theorem ListDecoder.length_le (D : ListDecoder κ R a ℓ) {L : ℕ} (hL : ListBound κ R a ℓ L)
    (F : LW (κ + R)) : (D.decode F).length ≤ L := by
  classical
  have := Fintype.ofFinite (Msgs ℓ κ)
  rw [← List.toFinset_card_of_nodup (D.nodup F)]
  refine le_trans ?_ (hL F)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.card_le_card fun V hV ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (D.mem_iff F V).mp (List.mem_toFinset.mp hV)⟩

/-- The rows of the encoder's matrix over `K` at the positions `T`, each from the `κ` values
`Ŵ_k(x)` of its position. -/
def encodeRows (κ R : ℕ) (T : Fin (2 ^ κ) → Fin (2 ^ (κ + R))) :
    Vector (Vector K (2 ^ κ)) (2 ^ κ) :=
  Vector.ofFn fun i ↦
    let w := Vector.ofFn fun k : Fin κ ↦ normW k (domainPt (T i))
    Vector.ofFn fun u : Fin (2 ^ κ) ↦ ∏ k : Fin κ, if u.val.testBit k then w[k] else 1

/-- The rows are the encoder's matrix. -/
theorem encodeRows_eq (T : Fin (2 ^ κ) → Fin (2 ^ (κ + R))) :
    (fun i j : Fin (2 ^ κ) ↦ (encodeRows κ R T)[i][j]) = encodeMatrix (RingHom.id K) κ R T := by
  funext i u
  simp [encodeRows, encodeMatrix, Fin.getElem_fin]

/-- The candidate of a family of `2 ^ κ` positions: the messages that, lane by lane, take the
word's values there, by Gaussian elimination of the encoder's matrix over `K`; `none` only if the
positions repeat. -/
def candidateAt (κ R ℓ : ℕ) (T : Fin (2 ^ κ) → Fin (2 ^ (κ + R))) (F : LW (κ + R)) :
    Option (Msgs ℓ κ) :=
  let rows := encodeRows κ R T
  let sols := Vector.ofFn fun u : Fin (2 ^ ℓ) ↦
    gaussSolve (2 ^ κ) (fun i j ↦ rows[i][j]) fun i ↦ F (T i) u
  if hs : ∀ u : Fin (2 ^ ℓ), sols[u].isSome then some fun u ↦ sols[u].get (hs u) else none

/-- The candidate, lane by lane. -/
theorem candidateAt_eq_some {T : Fin (2 ^ κ) → Fin (2 ^ (κ + R))} {F : LW (κ + R)}
    {V : Msgs ℓ κ} : candidateAt κ R ℓ T F = some V ↔ ∀ u : Fin (2 ^ ℓ),
      gaussSolve (2 ^ κ) (encodeMatrix (RingHom.id K) κ R T) (fun i ↦ F (T i) u) = some (V u) := by
  rw [← encodeRows_eq]
  simp only [candidateAt]
  split
  · rename_i hs
    simp only [Option.some.injEq, Fin.getElem_fin, Vector.getElem_ofFn] at hs ⊢
    constructor
    · rintro rfl u
      simp
    · intro h
      funext u
      simp [h u]
  · rename_i hs
    simp only [reduceCtorEq, false_iff, not_forall]
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, not_forall] at hs
    obtain ⟨u, hu⟩ := hs
    refine ⟨u, fun hx ↦ ?_⟩
    simp only [Fin.getElem_fin] at hx
    rw [hx] at hu
    exact hu rfl

/-- A candidate's encoding takes the word's values at the positions. -/
theorem candidateAt_sound {T : Fin (2 ^ κ) → Fin (2 ^ (κ + R))} {F : LW (κ + R)}
    {V : Msgs ℓ κ} (h : candidateAt κ R ℓ T F = some V) (i : Fin (2 ^ κ)) (u : Fin (2 ^ ℓ)) :
    encode (algebraMap K E) κ R (V u) (T i) = F (T i) u := by
  rw [encode_eq_sum_smul]
  simpa [Fin.getElem_fin] using gaussSolve_sound _ _ _ _ (candidateAt_eq_some.mp h u) i

/-- The candidate at distinct positions where the codeword of `V` agrees with the word is
`V`. -/
theorem candidateAt_of_agree (hb : κ + R ≤ 64) {T : Fin (2 ^ κ) → Fin (2 ^ (κ + R))}
    (hT : Function.Injective T) {F : LW (κ + R)} {V : Msgs ℓ κ}
    (hV : ∀ i (u : Fin (2 ^ ℓ)), encode (algebraMap K E) κ R (V u) (T i) = F (T i) u) :
    candidateAt κ R ℓ T F = some V := by
  refine candidateAt_eq_some.mpr fun u ↦ ?_
  obtain ⟨x, hx, hsol⟩ := gaussSolve_of_injective (encodeMatrix (RingHom.id K) κ R T)
    (fun i ↦ F (T i) u) (encodeMatrix_injective (RingHom.id K).injective hb hT)
  rw [hx]
  congr 1
  refine encode_eq_of_agree (algebraMap K E) hb (algebraMap K E).injective
    (Finset.univ.map ⟨T, hT⟩) (by simp) fun y hy ↦ ?_
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hy
  change encode (algebraMap K E) κ R _ (T i) = encode (algebraMap K E) κ R (V u) (T i)
  rw [hV i u, encode_eq_sum_smul]
  simpa [Fin.getElem_fin] using hsol i

/-- The candidate of a list of positions, when it has `2 ^ κ` of them. -/
def candidate (κ R ℓ : ℕ) (F : LW (κ + R)) (l : List (Fin (2 ^ (κ + R)))) : Option (Msgs ℓ κ) :=
  if h : l.length = 2 ^ κ then candidateAt κ R ℓ (listPositions l h) F else none

/-- The brute-force list: the candidates of every set of `2 ^ κ` positions, kept when within the
threshold, without repetition. -/
def bruteForceList (κ R a ℓ : ℕ) (F : LW (κ + R)) : List (Msgs ℓ κ) :=
  (((List.finRange (2 ^ (κ + R))).sublistsLen (2 ^ κ)).filterMap (candidate κ R ℓ F)).filter
    (fun V ↦ decide (Cl κ R a ℓ F V)) |>.dedup

/-- **The brute-force decoder**, at every threshold of at least `2 ^ κ`. -/
def ListDecoder.bruteForce (hdist : 2 ^ κ ≤ a) (hb : κ + R ≤ 64) : ListDecoder κ R a ℓ where
  decode := bruteForceList κ R a ℓ
  mem_iff := fun F V ↦ by
    simp only [bruteForceList, List.mem_dedup, List.mem_filter, List.mem_filterMap,
      decide_eq_true_eq]
    refine ⟨fun h ↦ h.2, fun hV ↦ ⟨⟨agreeList κ R ℓ F V, ?_, ?_⟩, hV⟩⟩
    · obtain ⟨hsub, hlen, -, -⟩ := agreeList_spec hdist hV
      exact List.mem_sublistsLen.mpr ⟨hsub, hlen⟩
    · obtain ⟨-, hlen, hnd, hmem⟩ := agreeList_spec hdist hV
      simp only [candidate, hlen, ↓reduceDIte]
      refine candidateAt_of_agree hb (listPositions_injective hlen hnd) fun i u ↦ ?_
      have hi := hmem _ (List.getElem_mem (h := by rw [hlen]; exact i.isLt))
      exact (Finset.mem_filter.mp hi).2 u
  nodup := fun _ ↦ List.nodup_dedup _

/-! ## The exact path -/

/-- The first `2 ^ κ` positions. -/
def firstPositions (κ R : ℕ) : Fin (2 ^ κ) → Fin (2 ^ (κ + R)) :=
  Fin.castLE (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right κ R))

/-- The exact path: the candidate of the first `2 ^ κ` positions, when its encoding is the whole
word. -/
def exactFast (κ R ℓ : ℕ) (F : LW (κ + R)) : Option (Msgs ℓ κ) :=
  (candidateAt κ R ℓ (firstPositions κ R) F).bind fun V ↦
    if ∀ y (u : Fin (2 ^ ℓ)), encode (algebraMap K E) κ R (V u) y = F y u then some V else none

/-- What the exact path returns is a codeword equal to the word. -/
theorem exactFast_spec {F : LW (κ + R)} {V : Msgs ℓ κ} (h : exactFast κ R ℓ F = some V) :
    ∀ y (u : Fin (2 ^ ℓ)), encode (algebraMap K E) κ R (V u) y = F y u := by
  obtain ⟨V', -, h'⟩ := Option.bind_eq_some_iff.mp h
  split at h'
  · rename_i hall
    cases h'
    exact hall
  · exact absurd h' (by simp)

/-- The exact path succeeds on every codeword. -/
theorem exactFast_of_codeword (hb : κ + R ≤ 64) {F : LW (κ + R)} {V : Msgs ℓ κ}
    (hV : ∀ y (u : Fin (2 ^ ℓ)), encode (algebraMap K E) κ R (V u) y = F y u) :
    exactFast κ R ℓ F = some V := by
  have hfirst : Function.Injective (firstPositions κ R) := Fin.castLE_injective _
  rw [exactFast, candidateAt_of_agree hb hfirst fun i u ↦ hV _ u, Option.bind_some]
  simp only [hV, implies_true, ↓reduceIte]

/-- **The list of a codeword is the codeword.** When the exact path returns `V`, every decoder at a
threshold `a` with `2 ^ κ ≤ a ≤ 2 ^ (κ + R)` returns exactly `V`: `V` agrees with the word
everywhere, and a codeword within the threshold agrees with `V` on `a ≥ 2 ^ κ` positions, so it is
`V`. -/
theorem exactFast_eq (D : ListDecoder κ R a ℓ) (hdist : 2 ^ κ ≤ a) (hle : a ≤ 2 ^ (κ + R))
    (hb : κ + R ≤ 64) {F : LW (κ + R)} {V : Msgs ℓ κ} (h : exactFast κ R ℓ F = some V) :
    ∀ V', V' ∈ D.decode F ↔ V' = V := by
  have hV := exactFast_spec h
  intro V'
  rw [D.mem_iff]
  constructor
  · intro hV'
    funext u
    refine encode_eq_of_agree (algebraMap K E) hb (algebraMap K E).injective
      (agreeSet κ R ℓ F V') (hdist.trans hV') fun y hy ↦ ?_
    rw [(Finset.mem_filter.mp hy).2 u, hV y u]
  · rintro rfl
    show a ≤ (Finset.univ.filter _).card
    rw [Finset.filter_true_of_mem fun y _ ↦ hV y, Finset.card_univ, Fintype.card_fin]
    exact hle

/-- A decoder that takes the exact path first and falls back to `D`. -/
def ListDecoder.exactFirst (D : ListDecoder κ R a ℓ) (hdist : 2 ^ κ ≤ a)
    (hle : a ≤ 2 ^ (κ + R)) (hb : κ + R ≤ 64) : ListDecoder κ R a ℓ where
  decode := fun F ↦ match exactFast κ R ℓ F with
    | some V => [V]
    | none => D.decode F
  mem_iff := fun F V ↦ by
    split
    · rename_i V₀ h
      rw [List.mem_singleton, ← D.mem_iff]
      exact (exactFast_eq D hdist hle hb h V).symm
    · exact D.mem_iff F V
  nodup := fun F ↦ by
    split
    · exact List.nodup_singleton _
    · exact D.nodup F

/-- **The decoder at exact agreement**: at the threshold of every position, the list of a word is
its codeword when it is one, which the exact path finds, and empty otherwise. -/
def ListDecoder.exact (hb : κ + R ≤ 64) : ListDecoder κ R (2 ^ (κ + R)) ℓ where
  decode := fun F ↦ (exactFast κ R ℓ F).toList
  mem_iff := fun F V ↦ by
    rw [Option.mem_toList]
    constructor
    · intro h
      have hV := exactFast_spec h
      show 2 ^ (κ + R) ≤ (Finset.univ.filter _).card
      rw [Finset.filter_true_of_mem fun y _ ↦ hV y, Finset.card_univ, Fintype.card_fin]
    · intro h
      refine exactFast_of_codeword hb fun y u ↦ ?_
      have hall : agreeSet κ R ℓ F V = Finset.univ := by
        refine Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) ?_)
        rw [Fintype.card_fin]
        exact h
      have hy : y ∈ agreeSet κ R ℓ F V := hall ▸ Finset.mem_univ y
      exact (Finset.mem_filter.mp hy).2 u
  nodup := fun F ↦ by
    cases exactFast κ R ℓ F <;> simp

/-! ## Codewords near a `K`-valued word -/

/-- **The list of a `K`-valued word is `K`-valued.** Every interleaved codeword within a threshold
of at least `2 ^ κ` of a word whose lanes take values in `K` has `K`-valued messages: on `2 ^ κ`
positions of agreement it is the interpolant of `K` values, found over `K`. -/
theorem isInK_of_cl (hdist : 2 ^ κ ≤ a) (hb : κ + R ≤ 64) {F : LW (κ + R)}
    (hF : ∀ y (u : Fin (2 ^ ℓ)), IsInK (F y u)) {V : Msgs ℓ κ} (hV : Cl κ R a ℓ F V)
    (u : Fin (2 ^ ℓ)) (x : Fin (2 ^ κ)) : IsInK (V u)[x] := by
  obtain ⟨-, hlen, hnd, hmem⟩ := agreeList_spec hdist hV
  set T := listPositions (agreeList κ R ℓ F V) hlen
  have hT := listPositions_injective hlen hnd
  have hagree : ∀ i, encode (algebraMap K E) κ R (V u) (T i) = F (T i) u := fun i ↦
    (Finset.mem_filter.mp (hmem _ (List.getElem_mem (h := by rw [hlen]; exact i.isLt)))).2 u
  obtain ⟨xK, -, hsol⟩ := gaussSolve_of_injective (encodeMatrix (RingHom.id K) κ R T)
    (fun i ↦ (F (T i) u).limb 0) (encodeMatrix_injective (RingHom.id K).injective hb hT)
  set mK : CMlPolynomialEval K κ := xK
  have hmK : CMlPolynomialEval.map (algebraMap K E) mK = V u := by
    refine encode_eq_of_agree (algebraMap K E) hb (algebraMap K E).injective
      (Finset.univ.map ⟨T, hT⟩) (by simp) fun y hy ↦ ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hy
    change encode (algebraMap K E) κ R _ (T i) = encode (algebraMap K E) κ R (V u) (T i)
    rw [encode_ofK, hagree i, ← sum_encodeMatrix]
    have hs := hsol i
    simp only [mK, Fin.getElem_fin, smul_eq_mul] at hs ⊢
    obtain ⟨c, hc⟩ := (isInK_iff _).mp (hF (T i) u)
    rw [hs, hc, limb_ofK]
    rfl
  rw [← hmK]
  exact (isInK_iff _).mpr ⟨mK[x], by simp [CMlPolynomialEval.map, Fin.getElem_fin]⟩

end Whir

end

end LeanerVM.Protocol
