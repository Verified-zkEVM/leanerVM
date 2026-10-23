/-
  LeanVM.Guest.B1.KeccakGkr.PackLoop

  B1 of the pack rounds' loop helpers (`__loop30` .. `__loop33`, one per `keccak_layer`
  specialization): two equality-mode rounds an iteration, from one round record to the next.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Plain

/-!
# The pack rounds' loop (`keccak_layer`, G:2640-2671)

`for x2 in mul_range(1, half_g)` in `keccak_layer` is lowered to a helper of parameters
`[x2, half_g, rounds, prev_point, point]` (`Data.core402` .. `Data.core405`, the same body but
for the self-call's name, `packLoopT`). At `x = g^j` it reads the record `rounds·x`, the two
coordinates `prev_point[2j], [2j + 1]` (`prev_point·x²`), runs two equality-mode rounds
(`eqRound`, as `keccak_round`), stores their challenges at `point[2j], [2j + 1]` and writes the
record `rounds·x·g` (`PackStep`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Two words absorbed and a squeeze -/

/-- **A squeeze of two read words**: `c₁`'s and `c₂`'s `fs_next` cells (`a`, `a + 10`), four
zeros and the capacity in one `KECCAK` atom, then `challenge_from_state`: the challenge `o + 19`
and the outputs `o + 8 .. o + 12` are `(⟨cap, []⟩.absorbAll [c₁, c₂]).squeeze`'s. -/
theorem sq2_atoms {a o : ℕ} {zs capV : List V} {cap : List E}
    (p1 : FsPackOk σ (.n a) (a + 1) dsObserve) (p2 : FsPackOk σ (.n (a + 10)) (a + 10 + 1) dsObserve)
    (hk : (Atom.keccak ([V.n (a + 7), .n (a + 9), .n (a + 17), .n (a + 19)] ++ zs ++ capV)
      ((List.range 13).map fun k ↦ .n (o + k)) false false).Holds rd σ)
    (hch : ChallengeOk σ (.n o) (.n (o + 1)) (o + 13)) (hz : zs.map σ = [0, 0, 0, 0])
    (hc : capV.map σ = cap) :
    σ (.n (o + 19)) = ((⟨cap, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 10))] dsObserve).squeeze.1 ∧
      [σ (.n (o + 8)), σ (.n (o + 9)), σ (.n (o + 10)), σ (.n (o + 11)), σ (.n (o + 12))] =
        ((⟨cap, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 10))] dsObserve).squeeze.2.cap := by
  obtain ⟨-, -, hcan, -⟩ := keccak_outs hk
  have c0 : IsCanonical128 (σ (.n (a + 7))) := hcan _ (by simp)
  have c2 : IsCanonical128 (σ (.n (a + 10 + 7))) := hcan _ (by simp)
  have s0 := fsNext_scalar p1 c0
  have s2 := fsNext_scalar p2 c2
  have habs : (⟨cap, []⟩ : Fs).absorbAll [σ (.n a), σ (.n (a + 10))] dsObserve =
      ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 10)), dsObserve)]⟩ := rfl
  have hin : ([V.n (a + 7), .n (a + 9), .n (a + 17), .n (a + 19)] ++ zs ++ capV).map σ =
      rateOf [(σ (.n a), dsObserve), (σ (.n (a + 10)), dsObserve)] ++ cap := by
    rw [rateOf_two, ← s0, ← s2, List.map_append, List.map_append, hz, hc]
    rfl
  have := squeeze_atom (s := ⟨cap, [(σ (.n a), dsObserve), (σ (.n (a + 10)), dsObserve)]⟩) hk hin
    (by simpa [range13_map] using hch)
  simp only [range13_map, List.drop, List.map_cons, List.map_nil] at this
  rw [habs]
  exact ⟨this.1, this.2⟩

/-! ## The loop body -/

/-- The loop body, the self-call named `name`. -/
def packLoopT (name : String) : List Stmt :=
  [.atom (.mul (.n 5) (.n 2) (.n 0)),
    .atom (.mul (.n 6) (.n 0) (.n 0)),
    .atom (.mul (.n 7) (.n 3) (.n 6)),
    .atom (.mul (.n 8) (.n 4) (.n 6)),
    .atom (.load (.n 9) (.n 5) 0),
    .atom (.load (.n 10) (.n 5) 16),
    .atom (.load (.n 11) (.n 5) 32),
    .atom (.load (.n 12) (.n 5) 48),
    .atom (.load (.n 13) (.n 5) 64),
    .atom (.load (.n 14) (.n 5) 80),
    .atom (.load (.n 15) (.n 5) 96),
    .atom (.load (.n 16) (.n 5) 112),
    .atom (.load (.n 17) (.n 7) 0),
    .atom (.load (.n 18) (.n 14) 0),
    .atom (.hint (.limbs (.n 18) [(.n 19), (.n 20), (.n 21)])),
    .atom (.const (.n 22) (word 1 0 0)),
    .atom (.assertInK (.n 21) (.n 22)),
    .atom (.const (.n 23) (word 0 0 1)),
    .atom (.mul (.n 24) (.n 23) (.n 21)),
    .atom (.add (.n 25) (.n 18) (.n 24)),
    .atom (.const (.n 26) (word 0 1 0)),
    .atom (.add (.n 27) (.n 21) (.n 26)),
    .atom (.load (.n 28) (.n 14) 1),
    .atom (.hint (.limbs (.n 28) [(.n 29), (.n 30), (.n 31)])),
    .atom (.const (.n 32) (word 1 0 0)),
    .atom (.assertInK (.n 31) (.n 32)),
    .atom (.const (.n 33) (word 0 0 1)),
    .atom (.mul (.n 34) (.n 33) (.n 31)),
    .atom (.add (.n 35) (.n 28) (.n 34)),
    .atom (.const (.n 36) (word 0 1 0)),
    .atom (.add (.n 37) (.n 31) (.n 36)),
    .atom (.const (.n 38) (word 1 0 0)),
    .atom (.const (.n 39) (word 0 0 0)),
    .atom (.const (.n 40) (word 0 0 0)),
    .atom (.const (.n 41) (word 0 0 0)),
    .atom (.const (.n 42) (word 0 0 0)),
    .atom (.keccak [.n 25, .n 27, .n 35, .n 37, .n 39, .n 40, .n 41, .n 42, .n 9, .n 10, .n 11, .n 12, .n 13] [.n 43, .n 44, .n 45, .n 46, .n 47, .n 48, .n 49, .n 50, .n 51, .n 52, .n 53, .n 54, .n 55] false false),
    .atom (.hint (.limbs (.n 44) [(.n 56)])),
    .atom (.add (.n 57) (.n 44) (.n 56)),
    .atom (.const (.n 58) (word 1 0 1)),
    .atom (.mul (.n 59) (.n 57) (.n 58)),
    .atom (.assertInK (.n 56) (.n 59)),
    .atom (.const (.n 60) (word 0 0 1)),
    .atom (.mul (.n 61) (.n 60) (.n 56)),
    .atom (.add (.n 62) (.n 43) (.n 61)),
    .atom (.load (.n 62) (.n 8) 0),
    .atom (.add (.n 63) (.n 17) (.n 62)),
    .atom (.const (.n 64) (word 1 0 0)),
    .atom (.add (.n 65) (.n 64) (.n 63)),
    .atom (.mul (.n 66) (.n 63) (.n 18)),
    .atom (.add (.n 67) (.n 15) (.n 66)),
    .atom (.mul (.n 68) (.n 62) (.n 62)),
    .atom (.add (.n 69) (.n 17) (.n 68)),
    .atom (.mul (.n 70) (.n 69) (.n 28)),
    .atom (.add (.n 71) (.n 67) (.n 70)),
    .atom (.mul (.n 72) (.n 65) (.n 71)),
    .atom (.mul (.n 73) (.n 16) (.n 65)),
    .atom (.load (.n 74) (.n 7) 1),
    .atom (.load (.n 75) (.n 14) 2),
    .atom (.hint (.limbs (.n 75) [(.n 76), (.n 77), (.n 78)])),
    .atom (.const (.n 79) (word 1 0 0)),
    .atom (.assertInK (.n 78) (.n 79)),
    .atom (.const (.n 80) (word 0 0 1)),
    .atom (.mul (.n 81) (.n 80) (.n 78)),
    .atom (.add (.n 82) (.n 75) (.n 81)),
    .atom (.const (.n 83) (word 0 1 0)),
    .atom (.add (.n 84) (.n 78) (.n 83)),
    .atom (.load (.n 85) (.n 14) 3),
    .atom (.hint (.limbs (.n 85) [(.n 86), (.n 87), (.n 88)])),
    .atom (.const (.n 89) (word 1 0 0)),
    .atom (.assertInK (.n 88) (.n 89)),
    .atom (.const (.n 90) (word 0 0 1)),
    .atom (.mul (.n 91) (.n 90) (.n 88)),
    .atom (.add (.n 92) (.n 85) (.n 91)),
    .atom (.const (.n 93) (word 0 1 0)),
    .atom (.add (.n 94) (.n 88) (.n 93)),
    .atom (.keccak [.n 82, .n 84, .n 92, .n 94, .n 39, .n 40, .n 41, .n 42, .n 51, .n 52, .n 53, .n 54, .n 55] [.n 95, .n 96, .n 97, .n 98, .n 99, .n 100, .n 101, .n 102, .n 103, .n 104, .n 105, .n 106, .n 107] false false),
    .atom (.hint (.limbs (.n 96) [(.n 108)])),
    .atom (.add (.n 109) (.n 96) (.n 108)),
    .atom (.const (.n 110) (word 1 0 1)),
    .atom (.mul (.n 111) (.n 109) (.n 110)),
    .atom (.assertInK (.n 108) (.n 111)),
    .atom (.const (.n 112) (word 0 0 1)),
    .atom (.mul (.n 113) (.n 112) (.n 108)),
    .atom (.add (.n 114) (.n 95) (.n 113)),
    .atom (.load (.n 114) (.n 8) 1),
    .atom (.add (.n 115) (.n 74) (.n 114)),
    .atom (.const (.n 116) (word 1 0 0)),
    .atom (.add (.n 117) (.n 116) (.n 115)),
    .atom (.mul (.n 118) (.n 115) (.n 75)),
    .atom (.add (.n 119) (.n 72) (.n 118)),
    .atom (.mul (.n 120) (.n 114) (.n 114)),
    .atom (.add (.n 121) (.n 74) (.n 120)),
    .atom (.mul (.n 122) (.n 121) (.n 85)),
    .atom (.add (.n 123) (.n 119) (.n 122)),
    .atom (.mul (.n 124) (.n 117) (.n 123)),
    .atom (.mul (.n 125) (.n 73) (.n 117)),
    .atom (.load (.n 103) (.n 5) 1),
    .atom (.load (.n 104) (.n 5) 17),
    .atom (.load (.n 105) (.n 5) 33),
    .atom (.load (.n 106) (.n 5) 49),
    .atom (.load (.n 107) (.n 5) 65),
    .atom (.const (.n 126) (word 16 0 0)),
    .atom (.mul (.n 127) (.n 14) (.n 126)),
    .atom (.load (.n 127) (.n 5) 81),
    .atom (.load (.n 124) (.n 5) 97),
    .atom (.load (.n 125) (.n 5) 113),
    .atom (.const (.n 128) (word 2 0 0)),
    .atom (.mul (.n 129) (.n 0) (.n 128)),
    .atom (.add (.n 130) (.n 129) (.n 1)),
    .atom (.const (.n 131) (word 2 0 0)),
    .atom (.mul (.n 132) (.n 0) (.n 131)),
    .callIf (.n 130) name [.n 132, .n 1, .n 2, .n 3, .n 4],
    .ret []]


/-- The four helpers' names, by `keccak_layer` specialization (`first`, `odd`). -/
def packLoopName : ℕ → ℕ → String
  | 1, 0 => "__loop30"
  | 1, _ => "__loop31"
  | _, 0 => "__loop32"
  | _, _ => "__loop33"

theorem packLoop_body30 : Data.core402.body = packLoopT "__loop30" := stmtsEqb_sound (by decide +kernel)
theorem packLoop_body31 : Data.core403.body = packLoopT "__loop31" := stmtsEqb_sound (by decide +kernel)
theorem packLoop_body32 : Data.core404.body = packLoopT "__loop32" := stmtsEqb_sound (by decide +kernel)
theorem packLoop_body33 : Data.core405.body = packLoopT "__loop33" := stmtsEqb_sound (by decide +kernel)

theorem find_packLoop30 : coreProgram.find? "__loop30" = some Data.core402 :=
  Program.find?_of_indexOf? (j := 402) (by decide +kernel) rfl
theorem find_packLoop31 : coreProgram.find? "__loop31" = some Data.core403 :=
  Program.find?_of_indexOf? (j := 403) (by decide +kernel) rfl
theorem find_packLoop32 : coreProgram.find? "__loop32" = some Data.core404 :=
  Program.find?_of_indexOf? (j := 404) (by decide +kernel) rfl
theorem find_packLoop33 : coreProgram.find? "__loop33" = some Data.core405 :=
  Program.find?_of_indexOf? (j := 405) (by decide +kernel) rfl

/-- **One iteration's meaning at `x`**: the record `rounds·x` holds a canonical capacity, a cursor,
a claim and a scale; the coordinates `r₀, r₁` at `prev_point·x²`; the four words at the cursor
are the two rounds' `(g₁, g₂)`; the two rounds' challenges are at `point·x²`, and the record
`rounds·x·g` holds the sponge after them, the cursor four words on, the claim and the scale. -/
def PackStep (rd : Reader) (rec pp pt x : E) : Prop :=
  ∃ (cap : List E) (cur claim scale r0 r1 g1 g2 g1' g2' : E),
    RoundRec rd (rec * x) 0 cap cur claim scale ∧ AllCanonical cap ∧
    LoadHolds rd (pp * x ^ 2) 0 r0 ∧ LoadHolds rd (pp * x ^ 2) 1 r1 ∧
    ReadsAt rd cur [g1, g2, g1', g2'] ∧
    let o1 := eqRound ⟨cap, []⟩ g1 g2 r0 claim scale
    let o2 := eqRound o1.2.2.2 g1' g2' r1 o1.2.1 o1.2.2.1
    LoadHolds rd (pt * x ^ 2) 0 o1.1 ∧ LoadHolds rd (pt * x ^ 2) 1 o2.1 ∧
    RoundRec rd (rec * x) 1 o2.2.2.2.cap (cur * gen ^ 4) o2.2.1 o2.2.2.1

theorem readsAt_four {p a b c d : E} (ha : LoadHolds rd p 0 a) (hb : LoadHolds rd p 1 b)
    (hc : LoadHolds rd p 2 c) (hd : LoadHolds rd p 3 d) : ReadsAt rd p [a, b, c, d] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  interval_cases k
  · exact ha
  · exact hb
  · exact hc
  · exact hd

theorem word_16 : word 16 0 0 = gen ^ 4 := by
  rw [show (16 : ℕ) = 2 ^ 4 from rfl]; exact word_two_pow (by decide)

set_option maxRecDepth 20000 in
/-- **The loop's step**: at depth `d + 1` and `x`, an iteration's meaning, and the call at `x·g`
one level shallower unless `x·g = half_g`. -/
theorem packLoop_step {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = packLoopT name) (hp : fn.params = [V.n 0, .n 1, .n 2, .n 3, .n 4]) (d : ℕ)
    (x hg rec pp pt : E) (h : coreProgram.relN rd (d + 1) name [x, hg, rec, pp, pt] []) :
    PackStep rd rec pp pt x ∧
      (x * gen + hg ≠ 0 → coreProgram.relN rd d name [x * gen, hg, rec, pp, pt] []) := by
  obtain ⟨fn', hf', σ, hpar, hbody⟩ := h
  rw [hf] at hf'
  cases hf'
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb] at hbody
  simp only [packLoopT, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hbody
  obtain ⟨e5, e6, e7, e8, L9_5_0, L10_5_16, L11_5_32, L12_5_48, L13_5_64, L14_5_80, L15_5_96,
    L16_5_112, L17_7_0, L18_14_0, -, e22, k21, e23, e24, e25, e26, e27, L28_14_1, -, e32, k31, e33,
    e34, e35, e36, e37, e38, e39, e40, e41, e42, hk36, -, e57, e58, e59, k56, e60, e61, e62,
    L62_8_0, e63, e64, e65, e66, e67, e68, e69, e70, e71, e72, e73, L74_7_1, L75_14_2, -, e79,
    k78, e80, e81, e82, e83, e84, L85_14_3, -, e89, k88, e90, e91, e92, e93, e94, hk76, -, e109,
    e110, e111, k108, e112, e113, e114, L114_8_1, e115, e116, e117, e118, e119, e120, e121, e122,
    e123, e124, e125, L103_5_1, L104_5_17, L105_5_33, L106_5_49, L107_5_65, e126, e127,
    L127_5_81, L124_5_97, L125_5_113, e128, e129, e130, e131, e132, -, hcall, -⟩ := hbody
  have hz : [V.n 39, .n 40, .n 41, .n 42].map σ = [0, 0, 0, 0] := by
    simp only [List.map_cons, List.map_nil, e39, e40, e41, e42, word_zero]
  have q0 := sq2_atoms (rd := rd) (a := 18) (o := 43) (zs := [.n 39, .n 40, .n 41, .n 42])
    (capV := [.n 9, .n 10, .n 11, .n 12, .n 13])
    (cap := [σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13)])
    ⟨e22, k21.1, k21.2, e23, e24, e25, e26, e27⟩ ⟨e32, k31.1, k31.2, e33, e34, e35, e36, e37⟩
    hk36 ⟨e57, e58, e59, k56.1, k56.2, e60, e61, e62⟩ hz rfl
  have q1 := sq2_atoms (rd := rd) (a := 75) (o := 95) (zs := [.n 39, .n 40, .n 41, .n 42])
    (capV := [.n 51, .n 52, .n 53, .n 54, .n 55])
    (cap := [σ (.n 51), σ (.n 52), σ (.n 53), σ (.n 54), σ (.n 55)])
    ⟨e79, k78.1, k78.2, e80, e81, e82, e83, e84⟩ ⟨e89, k88.1, k88.2, e90, e91, e92, e93, e94⟩
    hk76 ⟨e109, e110, e111, k108.1, k108.2, e112, e113, e114⟩ hz rfl
  simp only [Nat.reduceAdd] at q0 q1
  have hcan := hk36.2.2.1
  have hx2 : σ (.n 0) ^ 2 = σ (.n 6) := by rw [e6]; ring
  refine ⟨⟨[σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13)], σ (.n 14), σ (.n 15), σ (.n 16),
    σ (.n 17), σ (.n 74), σ (.n 18), σ (.n 28), σ (.n 75), σ (.n 85), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← e5]
    exact ⟨capAt_five L9_5_0 L10_5_16 L11_5_32 L12_5_48 L13_5_64, L14_5_80, L15_5_96, L16_5_112⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact hcan 8
    · exact hcan 9
    · exact hcan 10
    · exact hcan 11
    · exact hcan 12
  · rw [hx2, ← e7]; exact L17_7_0
  · rw [hx2, ← e7]; exact L74_7_1
  · exact readsAt_four L18_14_0 L28_14_1 L75_14_2 L85_14_3
  · have hs0 : ((⟨[σ (.n 9), σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 13)], []⟩ : Fs).absorbAll
        [σ (.n 18), σ (.n 28)] dsObserve).squeeze.2 =
        ⟨[σ (.n 51), σ (.n 52), σ (.n 53), σ (.n 54), σ (.n 55)], []⟩ := by
      rw [q0.2]; rfl
    simp only [eqRound]
    rw [hs0, ← q0.1]
    rw [← q1.1, ← q1.2, hx2, ← e8, ← e5]
    simp only [RoundRec, krCap, Nat.reduceMul, Nat.reduceAdd]
    refine ⟨L62_8_0, L114_8_1, capAt_five L103_5_1 L104_5_17 L105_5_33 L106_5_49 L107_5_65, ?_, ?_,
      ?_⟩
    · rw [e127, e126, word_16] at L127_5_81
      exact L127_5_81
    · simp only [e124, e117, e116, e115, e123, e119, e118, e122, e121, e120, e72, e65, e64, e63,
        e71, e67, e66, e70, e69, e68, word_one] at L124_5_97
      exact L124_5_97
    · simp only [e125, e117, e116, e115, e73, e65, e64, e63, word_one] at L125_5_113
      exact L125_5_113
  · intro hne
    have e : σ (.n 130) = σ (.n 0) * gen + σ (.n 1) := by rw [e130, e129, e128, word_gen]
    have e' : σ (.n 132) = σ (.n 0) * gen := by rw [e132, e131, word_gen]
    have := hcall (by rw [e]; exact hne)
    simpa [e'] using this

end
end LeanVM.Guest.B1.VerifySub
