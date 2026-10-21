/-
  LeanVM.Guest.B1.Tables.GkrLayerM

  `verify_bus_gkr`'s layer loop `__loop10` over a hash model: one radix-four layer of the GKR walk,
  a step of two levels of the specification's `gkrStep`, every hash answered by the model.
-/

module

public import LeanVM.Guest.B1.Tables.GkrLayer
public import LeanVM.Guest.B1.Tables.GkrLoopsM

/-!
# A layer of `verify_bus_gkr` over a hash model

`GkrLayer.lean` over a hash model `M`: the slot `GkrLayer` holds no hash and is unchanged;
`GkrPairStepM` is `GkrPairStep` with the layer's run `RunsToM M`; `loop10_stepM` reads the layer
off `__loop10`'s body under `M.sem`: the combiner's squeeze, the rounds (`gkr_roundsM`), the twelve
children's `fs_next` chained by the model (`fsM_chainAll`), the two coordinates' squeezes
(`sqAllM_two`), assembled by `runsToM_gkrStep`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel}

/-- One squeeze answered. -/
theorem sqAllM_one {c d1 : Digest} (h1 : sqCvM M c = some d1) :
    sqAllM M 1 c = some ([challengeOf d1], d1) := by
  simp [sqAllM, h1]

/-- Two squeezes answered. -/
theorem sqAllM_two {c d1 d2 : Digest} (h1 : sqCvM M c = some d1) (h2 : sqCvM M d1 = some d2) :
    sqAllM M 2 c = some ([challengeOf d1, challengeOf d2], d2) := by
  simp [sqAllM, h1, h2]

variable (M) in
/-- **A layer of two levels over the model** (`GkrPairStep`): the step's run `RunsToM M`. -/
def GkrPairStepM (rd : Reader) (layers dsb gmu x : E) : Prop :=
  ∀ j sh : ℕ, x = gen ^ j → LoadHolds rd (dsb * gmu) 0 (gen ^ sh) → j < 17 → sh < 2 →
    ∀ cv cur s row, GkrLayer rd layers (2 * j + sh) cv cur s row →
      ∃ ys s' cv', RunsToM M (gkrStep 2 s) cv ys s' cv' ∧ ReadsAt rd cur ys ∧
        GkrLayer rd layers (2 * j + sh + 2) cv' (cur * gen ^ ys.length) s' (row * gen ^ 40)

/-- **`__loop10`**, one iteration: the layer, then the loop at `x·g` while `x·g ≠ N`. -/
theorem loop10_stepM {rd : Reader} {N dsb gmu layers rounds x : E}
    (h : coreProgram.RelB M.sem rd "__loop10" [x, N, dsb, gmu, layers, rounds] []) :
    GkrPairStepM M rd layers dsb gmu x ∧
      (x * gen + N ≠ 0 →
        coreProgram.RelB M.sem rd "__loop10" [x * gen, N, dsb, gmu, layers, rounds] []) := by
  obtain ⟨σ, hp, hb, -⟩ := relB_pre find_loop10 core40_body l10Pre_noRet h
  simp only [show Fn.params Data.core40 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hp
  have hnr := l10Pre_noRet
  have a326 := holdsB_atom hnr hb 312 (.const (.n 326) (word 2 0 0)) (by decide +kernel)
  have a327 := holdsB_atom hnr hb 313 (.mul (.n 327) (.n 0) (.n 326)) (by decide +kernel)
  have a328 := holdsB_atom hnr hb 314 (.add (.n 328) (.n 327) (.n 1)) (by decide +kernel)
  have a329 := holdsB_atom hnr hb 315 (.const (.n 329) (word 2 0 0)) (by decide +kernel)
  have a330 := holdsB_atom hnr hb 316 (.mul (.n 330) (.n 0) (.n 329)) (by decide +kernel)
  have hc := holdsB_callIf hnr hb 317 (.n 328) "__loop10" [.n 330, .n 1, .n 2, .n 3, .n 4, .n 5]
    (by decide +kernel)
  simp only [Atom.Holds, word_gen, List.map_cons, List.map_nil] at a326 a327 a328 a329 a330 hc
  refine ⟨?_, fun hne => ?_⟩
  swap
  · have := hc (by rw [a328, a327, a326]; exact hne)
    rw [a330, a329] at this
    exact this
  intro j sh hx hsh hj hsh2 cv cur s row hL
  obtain ⟨g0, g1, g2, gv, g3, g4, g5, g6, gpl, gpt⟩ := hL
  -- the slot of `L`
  have a6 := holdsB_atom hnr hb 0 (.mul (.n 6) (.n 0) (.n 0)) (by decide +kernel)
  have a7 := holdsB_atom hnr hb 1 (.mul (.n 7) (.n 2) (.n 3)) (by decide +kernel)
  have l8 := holdsB_atom hnr hb 2 (.load (.n 8) (.n 7) 0) (by decide +kernel)
  have a9 := holdsB_atom hnr hb 3 (.mul (.n 9) (.n 6) (.n 8)) (by decide +kernel)
  have a10 := holdsB_atom hnr hb 4 (.mul (.n 10) (.n 9) (.n 9)) (by decide +kernel)
  have a11 := holdsB_atom hnr hb 5 (.mul (.n 11) (.n 10) (.n 10)) (by decide +kernel)
  have a12 := holdsB_atom hnr hb 6 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel)
  have a13 := holdsB_atom hnr hb 7 (.mul (.n 13) (.n 4) (.n 12)) (by decide +kernel)
  have l14 := holdsB_atom hnr hb 8 (.load (.n 14) (.n 13) 0) (by decide +kernel)
  have l15 := holdsB_atom hnr hb 9 (.load (.n 15) (.n 13) 1) (by decide +kernel)
  have sq1 := holdsB_squeezeAt hnr hb 10 (.n 14) (.n 15) 16 (by decide +kernel)
  have l30 := holdsB_atom hnr hb 24 (.load (.n 30) (.n 13) 6) (by decide +kernel)
  have a32 := holdsB_atom hnr hb 26 (.mul (.n 32) (.n 31) (.n 31)) (by decide +kernel)
  have a33 := holdsB_atom hnr hb 27 (.mul (.n 33) (.n 32) (.n 32)) (by decide +kernel)
  have a34 := holdsB_atom hnr hb 28 (.mul (.n 34) (.n 5) (.n 33)) (by decide +kernel)
  have s21 := holdsB_atom hnr hb 29 (.load (.n 21) (.n 34) 0) (by decide +kernel)
  have s22 := holdsB_atom hnr hb 30 (.load (.n 22) (.n 34) 1) (by decide +kernel)
  have l35 := holdsB_atom hnr hb 31 (.load (.n 35) (.n 13) 2) (by decide +kernel)
  have s35 := holdsB_atom hnr hb 32 (.load (.n 35) (.n 34) 2) (by decide +kernel)
  have l36 := holdsB_atom hnr hb 33 (.load (.n 36) (.n 13) 3) (by decide +kernel)
  have l37 := holdsB_atom hnr hb 34 (.load (.n 37) (.n 13) 4) (by decide +kernel)
  have l38 := holdsB_atom hnr hb 35 (.load (.n 38) (.n 13) 5) (by decide +kernel)
  have a39 := holdsB_atom hnr hb 36 (.mul (.n 39) (.n 29) (.n 38)) (by decide +kernel)
  have a40 := holdsB_atom hnr hb 37 (.add (.n 40) (.n 37) (.n 39)) (by decide +kernel)
  have a41 := holdsB_atom hnr hb 38 (.mul (.n 41) (.n 29) (.n 40)) (by decide +kernel)
  have a42 := holdsB_atom hnr hb 39 (.add (.n 42) (.n 36) (.n 41)) (by decide +kernel)
  have s42 := holdsB_atom hnr hb 40 (.load (.n 42) (.n 34) 3) (by decide +kernel)
  have a43 := holdsB_atom hnr hb 41 (.const (.n 43) (word 1 0 0)) (by decide +kernel)
  have a44 := holdsB_atom hnr hb 42 (.add (.n 44) (.n 43) (.n 9)) (by decide +kernel)
  have a45 := holdsB_atom hnr hb 43 (.const (.n 45) (word 1 0 0)) (by decide +kernel)
  have a46 := holdsB_atom hnr hb 44 (.const (.n 46) (word 1099511627776 0 0)) (by decide +kernel)
  have a47 := holdsB_atom hnr hb 45 (.mul (.n 47) (.n 30) (.n 46)) (by decide +kernel)
  have c101 := holdsB_callIf hnr hb 46 (.n 44) "__loop101" [.n 45, .n 9, .n 5, .n 31, .n 30, .n 47]
    (by decide +kernel)
  -- the tail
  have a48 := holdsB_atom hnr hb 47 (.mul (.n 48) (.n 31) (.n 9)) (by decide +kernel)
  have a49 := holdsB_atom hnr hb 48 (.mul (.n 49) (.n 48) (.n 48)) (by decide +kernel)
  have a50 := holdsB_atom hnr hb 49 (.mul (.n 50) (.n 49) (.n 49)) (by decide +kernel)
  have a51 := holdsB_atom hnr hb 50 (.mul (.n 51) (.n 5) (.n 50)) (by decide +kernel)
  have l52 := holdsB_atom hnr hb 51 (.load (.n 52) (.n 51) 0) (by decide +kernel)
  have l53 := holdsB_atom hnr hb 52 (.load (.n 53) (.n 51) 1) (by decide +kernel)
  have l54 := holdsB_atom hnr hb 53 (.load (.n 54) (.n 51) 2) (by decide +kernel)
  have l55 := holdsB_atom hnr hb 54 (.load (.n 55) (.n 51) 3) (by decide +kernel)
  -- the children
  have fsb := fun i hi => holdsB_fsNextAt hnr hb (55 + 14 * i) _ _ _ i _ (l10_fs_blocks i hi)
  have cpb := fun i hi => holdsB_atom hnr hb (68 + 14 * i)
    (.copy (.n (71 + 16 * i)) (.n (56 + 16 * i)))
    (by rw [l10_copy_blocks i hi, Bool.true_and]; rfl)
  have a248 := holdsB_atom hnr hb 223 (.mul (.n 248) (.n 199) (.n 215)) (by decide +kernel)
  have a249 := holdsB_atom hnr hb 224 (.mul (.n 249) (.n 248) (.n 231)) (by decide +kernel)
  have a250 := holdsB_atom hnr hb 225 (.mul (.n 250) (.n 249) (.n 247)) (by decide +kernel)
  have a251 := holdsB_atom hnr hb 226 (.const (.n 251) (word 0 0 0)) (by decide +kernel)
  have a252 := holdsB_atom hnr hb 227 (.mul (.n 252) (.n 29) (.n 251)) (by decide +kernel)
  have a253 := holdsB_atom hnr hb 228 (.add (.n 253) (.n 250) (.n 252)) (by decide +kernel)
  have a254 := holdsB_atom hnr hb 229 (.mul (.n 254) (.n 135) (.n 151)) (by decide +kernel)
  have a255 := holdsB_atom hnr hb 230 (.mul (.n 255) (.n 254) (.n 167)) (by decide +kernel)
  have a256 := holdsB_atom hnr hb 231 (.mul (.n 256) (.n 255) (.n 183)) (by decide +kernel)
  have a257 := holdsB_atom hnr hb 232 (.mul (.n 257) (.n 29) (.n 253)) (by decide +kernel)
  have a258 := holdsB_atom hnr hb 233 (.add (.n 258) (.n 256) (.n 257)) (by decide +kernel)
  have a259 := holdsB_atom hnr hb 234 (.mul (.n 259) (.n 71) (.n 87)) (by decide +kernel)
  have a260 := holdsB_atom hnr hb 235 (.mul (.n 260) (.n 259) (.n 103)) (by decide +kernel)
  have a261 := holdsB_atom hnr hb 236 (.mul (.n 261) (.n 260) (.n 119)) (by decide +kernel)
  have a262 := holdsB_atom hnr hb 237 (.mul (.n 262) (.n 29) (.n 258)) (by decide +kernel)
  have a263 := holdsB_atom hnr hb 238 (.add (.n 263) (.n 261) (.n 262)) (by decide +kernel)
  have ae := holdsB_atom hnr hb 239 (.assertEq (.n 55) (.n 263)) (by decide +kernel)
  have sq2 := holdsB_squeezeAt hnr hb 240 (.n 245) (.n 246) 264 (by decide +kernel)
  have sq3 := holdsB_squeezeAt hnr hb 254 (.n 269) (.n 270) 278 (by decide +kernel)
  -- the slot of `L + 2`
  have t277 := holdsB_atom hnr hb 268 (.load (.n 277) (.n 30) 40) (by decide +kernel)
  have t291 := holdsB_atom hnr hb 269 (.load (.n 291) (.n 30) 41) (by decide +kernel)
  have t283 := holdsB_atom hnr hb 270 (.load (.n 283) (.n 13) 16) (by decide +kernel)
  have t284 := holdsB_atom hnr hb 271 (.load (.n 284) (.n 13) 17) (by decide +kernel)
  have a292 := holdsB_atom hnr hb 272 (.const (.n 292) (word 4096 0 0)) (by decide +kernel)
  have a293 := holdsB_atom hnr hb 273 (.mul (.n 293) (.n 54) (.n 292)) (by decide +kernel)
  have t293 := holdsB_atom hnr hb 274 (.load (.n 293) (.n 13) 18) (by decide +kernel)
  have a294 := holdsB_atom hnr hb 275 (.add (.n 294) (.n 71) (.n 87)) (by decide +kernel)
  have a295 := holdsB_atom hnr hb 276 (.mul (.n 295) (.n 277) (.n 294)) (by decide +kernel)
  have a296 := holdsB_atom hnr hb 277 (.add (.n 296) (.n 71) (.n 295)) (by decide +kernel)
  have a297 := holdsB_atom hnr hb 278 (.add (.n 297) (.n 103) (.n 119)) (by decide +kernel)
  have a298 := holdsB_atom hnr hb 279 (.mul (.n 298) (.n 277) (.n 297)) (by decide +kernel)
  have a299 := holdsB_atom hnr hb 280 (.add (.n 299) (.n 103) (.n 298)) (by decide +kernel)
  have a300 := holdsB_atom hnr hb 281 (.add (.n 300) (.n 296) (.n 299)) (by decide +kernel)
  have a301 := holdsB_atom hnr hb 282 (.mul (.n 301) (.n 291) (.n 300)) (by decide +kernel)
  have a302 := holdsB_atom hnr hb 283 (.add (.n 302) (.n 296) (.n 301)) (by decide +kernel)
  have t302 := holdsB_atom hnr hb 284 (.load (.n 302) (.n 13) 19) (by decide +kernel)
  have a303 := holdsB_atom hnr hb 285 (.add (.n 303) (.n 135) (.n 151)) (by decide +kernel)
  have a304 := holdsB_atom hnr hb 286 (.mul (.n 304) (.n 277) (.n 303)) (by decide +kernel)
  have a305 := holdsB_atom hnr hb 287 (.add (.n 305) (.n 135) (.n 304)) (by decide +kernel)
  have a306 := holdsB_atom hnr hb 288 (.add (.n 306) (.n 167) (.n 183)) (by decide +kernel)
  have a307 := holdsB_atom hnr hb 289 (.mul (.n 307) (.n 277) (.n 306)) (by decide +kernel)
  have a308 := holdsB_atom hnr hb 290 (.add (.n 308) (.n 167) (.n 307)) (by decide +kernel)
  have a309 := holdsB_atom hnr hb 291 (.add (.n 309) (.n 305) (.n 308)) (by decide +kernel)
  have a310 := holdsB_atom hnr hb 292 (.mul (.n 310) (.n 291) (.n 309)) (by decide +kernel)
  have a311 := holdsB_atom hnr hb 293 (.add (.n 311) (.n 305) (.n 310)) (by decide +kernel)
  have t311 := holdsB_atom hnr hb 294 (.load (.n 311) (.n 13) 20) (by decide +kernel)
  have a312 := holdsB_atom hnr hb 295 (.add (.n 312) (.n 199) (.n 215)) (by decide +kernel)
  have a313 := holdsB_atom hnr hb 296 (.mul (.n 313) (.n 277) (.n 312)) (by decide +kernel)
  have a314 := holdsB_atom hnr hb 297 (.add (.n 314) (.n 199) (.n 313)) (by decide +kernel)
  have a315 := holdsB_atom hnr hb 298 (.add (.n 315) (.n 231) (.n 247)) (by decide +kernel)
  have a316 := holdsB_atom hnr hb 299 (.mul (.n 316) (.n 277) (.n 315)) (by decide +kernel)
  have a317 := holdsB_atom hnr hb 300 (.add (.n 317) (.n 231) (.n 316)) (by decide +kernel)
  have a318 := holdsB_atom hnr hb 301 (.add (.n 318) (.n 314) (.n 317)) (by decide +kernel)
  have a319 := holdsB_atom hnr hb 302 (.mul (.n 319) (.n 291) (.n 318)) (by decide +kernel)
  have a320 := holdsB_atom hnr hb 303 (.add (.n 320) (.n 314) (.n 319)) (by decide +kernel)
  have t320 := holdsB_atom hnr hb 304 (.load (.n 320) (.n 13) 21) (by decide +kernel)
  have a321 := holdsB_atom hnr hb 305 (.const (.n 321) (word 1099511627776 0 0)) (by decide +kernel)
  have a322 := holdsB_atom hnr hb 306 (.mul (.n 322) (.n 30) (.n 321)) (by decide +kernel)
  have t322 := holdsB_atom hnr hb 307 (.load (.n 322) (.n 13) 22) (by decide +kernel)
  simp only [Atom.Holds, word_one, word_zero, word_g40, word_g12, List.map_cons,
    List.map_nil] at *
  -- the slot of `L`
  rw [a7] at l8
  have e8 : σ (.n 8) = gen ^ sh := loadHolds_unique l8 hsh
  have e9 : σ (.n 9) = gen ^ (2 * j + sh) := by
    rw [a9, a6, e8, hx, ← pow_add, ← pow_add]; exact congrArg (gen ^ ·) (by omega)
  have hL : ∀ k w, LoadHolds rd (σ (.n 13)) k w ↔
      LoadHolds rd (σ (.n 4)) (8 * (2 * j + sh) + k) w := by
    intro k w
    rw [show σ (.n 13) = σ (.n 4) * gen ^ (8 * (2 * j + sh)) by rw [a13, a12, a11, a10, e9]; ring,
      loadHolds_gen_pow_mul]
  have e14 : σ (.n 14) = (digestScalars cv).1 := loadHolds_unique ((hL 0 _).mp l14) g0
  have e15 : σ (.n 15) = (digestScalars cv).2 := loadHolds_unique ((hL 1 _).mp l15) g1
  have e30 : σ (.n 30) = row := loadHolds_unique ((hL 6 _).mp l30) g6
  have e35 : σ (.n 35) = cur := loadHolds_unique ((hL 2 _).mp l35) g2
  have e36 : σ (.n 36) = s.values.getD 0 0 := loadHolds_unique ((hL 3 _).mp l36) g3
  have e37 : σ (.n 37) = s.values.getD 1 0 := loadHolds_unique ((hL 4 _).mp l37) g4
  have e38 : σ (.n 38) = s.values.getD 2 0 := loadHolds_unique ((hL 5 _).mp l38) g5
  obtain ⟨cv0, cL, hcv0, hL0, hsq, h29⟩ := sq1
  have ecv : cv0 = cv := digestScalars_injective (by rw [← hcv0, e14, e15])
  subst ecv
  have e34 : σ (.n 34) = σ (.n 5) * σ (.n 31) ^ 4 := by rw [a34, a33, a32]; ring
  rw [e34] at s21 s22 s35 s42
  rw [e35] at s35
  have e21 : σ (.n 21) = (digestScalars cL).1 := congrArg Prod.fst hsq
  have e22 : σ (.n 22) = (digestScalars cL).2 := congrArg Prod.snd hsq
  rw [e21] at s21
  rw [e22] at s22
  have e42 : σ (.n 42) = polyEval s.values (challengeOf cL) := by
    rw [a42, a41, a40, a39, e36, e37, e38, h29, values_three gv, polyEval_three]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
  -- the rounds
  have hR : ∀ r < 2 * j + sh,
      GkrRoundM M rd (σ (.n 5)) (σ (.n 31)) (σ (.n 30)) (σ (.n 47)) (gen ^ r) :=
    loop_soundB (ps := [σ (.n 9), σ (.n 5), σ (.n 31), σ (.n 30), σ (.n 47)]) (N := σ (.n 9))
      (by unfold ordG; omega) e9 (fun x hx => loop101_stepM hx) (fun hne => by
        have := c101 (by rw [a44, a43]; exact hne)
        rw [a45] at this
        exact this)
  obtain ⟨ws, chs, cl, cvS, hwl, hws, hchl, hchs, hsc, u0, u1, u2, u3⟩ :=
    gkr_roundsM (2 * j + sh) (σ (.n 31)) (σ (.n 30)) (σ (.n 47)) cL cur (σ (.n 42)) s.point
      hR gpl (by rw [e30]; exact gpt) s21 s22 s35 s42
  rw [e42] at hsc
  -- the tail
  have hT : ∀ k w, LoadHolds rd (σ (.n 51)) k w ↔
      LoadHolds rd (σ (.n 5) * σ (.n 31) ^ 4) (4 * (2 * j + sh) + k) w := by
    intro k w
    rw [show σ (.n 51) = σ (.n 5) * σ (.n 31) ^ 4 * gen ^ (4 * (2 * j + sh)) by
      rw [a51, a50, a49, a48, e9]; ring, loadHolds_gen_pow_mul]
  have e52 : σ (.n 52) = (digestScalars cvS).1 := loadHolds_unique ((hT 0 _).mp l52) u0
  have e53 : σ (.n 53) = (digestScalars cvS).2 := loadHolds_unique ((hT 1 _).mp l53) u1
  have e54 : σ (.n 54) = cur * gen ^ (4 * (2 * j + sh)) := loadHolds_unique ((hT 2 _).mp l54) u2
  have e55 : σ (.n 55) = cl := loadHolds_unique ((hT 3 _).mp l55) u3
  -- the children
  have f0 := (fsb 0 (by decide)).2
  have c0 := cpb 0 (by decide)
  have f1 := (fsb 1 (by decide)).2
  have c1 := cpb 1 (by decide)
  have f2 := (fsb 2 (by decide)).2
  have c2 := cpb 2 (by decide)
  have f3 := (fsb 3 (by decide)).2
  have c3 := cpb 3 (by decide)
  have f4 := (fsb 4 (by decide)).2
  have c4 := cpb 4 (by decide)
  have f5 := (fsb 5 (by decide)).2
  have c5 := cpb 5 (by decide)
  have f6 := (fsb 6 (by decide)).2
  have c6 := cpb 6 (by decide)
  have f7 := (fsb 7 (by decide)).2
  have c7 := cpb 7 (by decide)
  have f8 := (fsb 8 (by decide)).2
  have c8 := cpb 8 (by decide)
  have f9 := (fsb 9 (by decide)).2
  have c9 := cpb 9 (by decide)
  have f10 := (fsb 10 (by decide)).2
  have c10 := cpb 10 (by decide)
  have f11 := (fsb 11 (by decide)).2
  have c11 := cpb 11 (by decide)
  simp only [l10S, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, OfNat.ofNat_ne_zero,
    Nat.succ_ne_zero] at f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
  obtain ⟨d0, o0, k0⟩ := fsM_chainAll (obsAllM_nil cvS)
    (show (σ (.n 52), σ (.n 53)) = digestScalars cvS by rw [e52, e53]) f0
  obtain ⟨d1, o1, k1⟩ := fsM_chainAll o0 k0 f1
  obtain ⟨d2, o2, k2⟩ := fsM_chainAll o1 k1 f2
  obtain ⟨d3, o3, k3⟩ := fsM_chainAll o2 k2 f3
  obtain ⟨d4, o4, k4⟩ := fsM_chainAll (obsAllM_nil d3) k3 f4
  obtain ⟨d5, o5, k5⟩ := fsM_chainAll o4 k4 f5
  obtain ⟨d6, o6, k6⟩ := fsM_chainAll o5 k5 f6
  obtain ⟨d7, o7, k7⟩ := fsM_chainAll o6 k6 f7
  obtain ⟨d8, o8, k8⟩ := fsM_chainAll (obsAllM_nil d7) k7 f8
  obtain ⟨d9, o9, k9⟩ := fsM_chainAll o8 k8 f9
  obtain ⟨d10, o10, k10⟩ := fsM_chainAll o9 k9 f10
  obtain ⟨d11, o11, k11⟩ := fsM_chainAll o10 k10 f11
  simp only [List.nil_append, List.cons_append] at o3 o7 o11
  obtain ⟨cvA, dA, hA, hdA, hA', h277⟩ := sq2
  obtain ⟨cvB, dB, hB, hdB, hB', h291⟩ := sq3
  rw [hA] at k11
  have ecA := digestScalars_injective k11
  subst ecA
  rw [hA'] at hB
  have ecB := digestScalars_injective hB
  subst ecB
  have hreq : cl = polyEval [prodE [σ (.n 56), σ (.n 72), σ (.n 88), σ (.n 104)],
      prodE [σ (.n 120), σ (.n 136), σ (.n 152), σ (.n 168)],
      prodE [σ (.n 184), σ (.n 200), σ (.n 216), σ (.n 232)]] (challengeOf cL) := by
    rw [← e55, e_add_eq_zero_iff.mp ae, a263, a262, a261, a260, a259, a258, a257, a256, a255, a254,
      a253, a252, a251, a250, a249, a248, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, h29,
      polyEval_three, prodE_four, prodE_four, prodE_four]
    ring
  have hrun := runsToM_gkrStep 2 hL0 hsc rfl rfl rfl o3 o7 o11 hreq (sqAllM_two hdA hdB)
  rw [← h277, ← h291] at hrun
  refine ⟨_, _, _, hrun, ?_, ?_⟩
  · refine readsAt_append_pow hws ?_
    rw [hwl, ← e54]
    intro k hk
    have hk' : k < 12 := by simpa using hk
    obtain ⟨hl, -⟩ := fsb k hk'
    interval_cases k <;> exact hl
  have hN : ∀ k w, LoadHolds rd (σ (.n 13)) (16 + k) w ↔
      LoadHolds rd (σ (.n 4)) (8 * (2 * j + sh + 2) + k) w := by
    intro k w
    rw [hL, show 8 * (2 * j + sh) + (16 + k) = 8 * (2 * j + sh + 2) + k by ring]
  refine ⟨(hN 0 _).mp ?_, (hN 1 _).mp ?_, (hN 2 _).mp ?_, rfl, (hN 3 _).mp ?_, (hN 4 _).mp ?_,
    (hN 5 _).mp ?_, (hN 6 _).mp ?_, by simp [hchl], ?_⟩
  · rw [← (congrArg Prod.fst hB')]; exact t283
  · rw [← (congrArg Prod.snd hB')]; exact t284
  · have : cur * gen ^ (ws ++ ([σ (.n 56), σ (.n 72), σ (.n 88), σ (.n 104)] ++
        ([σ (.n 120), σ (.n 136), σ (.n 152), σ (.n 168)] ++
          [σ (.n 184), σ (.n 200), σ (.n 216), σ (.n 232)]))).length = σ (.n 293) := by
      rw [a293, a292, e54, mul_assoc, ← pow_add]
      simp only [List.length_append, hwl, List.length_cons, List.length_nil]
    rw [this]; exact t293
  · have : σ (.n 302) = multilinearEval [σ (.n 56), σ (.n 72), σ (.n 88), σ (.n 104)]
        [σ (.n 277), σ (.n 291)] := by
      rw [multilinearEval_four, a302, a301, a300, a299, a298, a297, a296, a295, a294, c0, c1, c2,
        c3]
      ring
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero]
    rw [← this]; exact t302
  · have : σ (.n 311) = multilinearEval [σ (.n 120), σ (.n 136), σ (.n 152), σ (.n 168)]
        [σ (.n 277), σ (.n 291)] := by
      rw [multilinearEval_four, a311, a310, a309, a308, a307, a306, a305, a304, a303, c4, c5, c6,
        c7]
      ring
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    rw [← this]; exact t311
  · have : σ (.n 320) = multilinearEval [σ (.n 184), σ (.n 200), σ (.n 216), σ (.n 232)]
        [σ (.n 277), σ (.n 291)] := by
      rw [multilinearEval_four, a320, a319, a318, a317, a316, a315, a314, a313, a312, c8, c9, c10,
        c11]
      ring
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    rw [← this]; exact t320
  · rw [a322, a321, e30] at t322; exact t322
  · rw [a47, a46, e30] at hchs
    refine readsAt_append_pow ?_
      (by simp only [List.length_cons, List.length_nil, Nat.reduceAdd]; exact hchs)
    intro k hk
    have hk' : k < 2 := by simpa using hk
    rw [loadHolds_gen_pow_mul]
    rw [e30] at t277 t291
    interval_cases k
    · exact t277
    · exact t291


end
end LeanVM.Guest.B1.VerifySub
