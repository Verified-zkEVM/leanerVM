/-
  LeanVM.Guest.B1.Whir.Levels

  The template's levels run the Spec's levels up to the tail.
-/

module

public import LeanVM.Guest.B1.Whir.Level
public import LeanVM.Guest.B1.Whir.LevelSpec

/-!
# The levels (G:1343-1502)

`whirLevelsHead`: `whirLevelsOpen` without its tail (`whirLevelsOpen_eq`). `osLevels_sound`: the
template's levels, the configuration's facts holding level by level (`LevelsOk`) and the callees
by their meanings (`CalleesOk`), run `whirLevelsHead`; they leave the final message, every
level's record (`RecStored`), the fold challenges in `fold_challenges` and the guest's state for
the tail.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- `whirLevelsOpen` up to the tail: the levels' heads. -/
def whirLevelsHead (logN : ℕ) : ℕ → List Whir.Level → WhirState → Prog (List E × ℕ × WhirState)
  | _, [], _ => Prog.fail
  | index, [level], s => levelHead logN index level [] s
  | index, level :: next :: rest, s =>
    (levelHead logN index level (next :: rest) s).bind fun r ↦
      whirLevelsHead logN (index + 1) (next :: rest) r.2.2

/-- **The levels, then the tail.** -/
theorem whirLevelsOpen_eq (logN laneFolds : ℕ) : ∀ (index : ℕ) (cfg : List Whir.Level)
    (s : WhirState), cfg ≠ [] →
    whirLevelsOpen logN laneFolds index cfg s =
      (whirLevelsHead logN index cfg s).bind fun r ↦ levelTail laneFolds r.2.1 r.1 r.2.2
  | _, [], _, h => absurd rfl h
  | index, [level], s, _ => by rw [whirLevelsOpen_head]; rfl
  | index, level :: next :: rest, s, _ => by
    rw [whirLevelsOpen_head, whirLevelsHead, Prog.bind_assoc]
    refine prog_bind_congr fun r ↦ ?_
    exact whirLevelsOpen_eq logN laneFolds (index + 1) (next :: rest) r.2.2 (by simp)

/-- The configuration's facts, level by level. -/
def LevelsOk (c : OsCfg) (logN : ℕ) : ℕ → List OsLv → List Whir.Level → Prop
  | lvl, [lv], [level] => LvB c lvl lv level lv.logCols ∧ level.fold = lv.folds ∧
      1 ≤ lv.folds ∧ logN - (lv.foldsOff + lv.folds) = lv.logCols ∧
      2 ^ lv.logCols = c.yrLen ∧ lvl = c.yrLevel
  | lvl, lv :: lv' :: lvs, level :: next :: cfg => LvB c lvl lv level lv.logCols ∧
      level.fold = lv.folds ∧ 1 ≤ lv.folds ∧ logN - (lv.foldsOff + lv.folds) = lv.logCols ∧
      1 ≤ lv.logCols ∧ (lvl + 1) * ligColsCap < u128Bound ∧ lvl ≠ c.yrLevel ∧
      lv'.foldsOff = lv.foldsOff + lv.folds ∧
      levelShape lv.logCols next (3 * 2 ^ next.fold) = (lv'.depth, lvWidth (lvl + 1) lv') ∧
      LevelsOk c logN (lvl + 1) (lv' :: lvs) (next :: cfg)
  | _, _, _ => False

/-- The callees, level by level. -/
def CalleesOk (rd : Reader) (c : OsCfg) : ℕ → List OsLv → Prop
  | _, [] => True
  | lvl, lv :: lvs => LvCallees rd c lvl lv ∧ CalleesOk rd c (lvl + 1) lvs

/-- **The levels** run `whirLevelsHead`. -/
theorem osLevels_sound {c : OsCfg} {logN : ℕ} : ∀ (lvs : List OsLv) (cfg : List Whir.Level)
    (lvl : ℕ) (st : OsSt) (ws : WhirState) (R : List (Digest × ℕ × ℕ)) (root : Digest),
    LevelsOk c logN lvl lvs cfg → CalleesOk rd c lvl lvs →
    LvIn rd σ lvl (lvs.headD default) st ws R root →
    AllOk (coreProgram.Rel rd) rd σ (osLevels c lvl lvs st).1 →
    ∃ (xs : List E) (os : List Opening) (R' : List (Digest × ℕ × ℕ)) (ms : List E)
      (ws' : WhirState) (rs : List OsRec),
      ReadsAt rd (st.cur σ) xs ∧
      RunsWith (whirLevelsHead logN lvl cfg ws) (st.F σ) xs os R
        (ms, (lvs.getLastD default).logCols, ws') ((osLevels c lvl lvs st).2.F σ) R' ∧
      ms.length = c.yrLen ∧ ReadsAt rd (σ (.n osFmsg)) ms ∧
      ws'.glued = ws.glued ++ rs.flatMap recClaims ∧ rs.length = lvs.length ∧
      (∀ i (hi : i < rs.length) (hi' : i < lvs.length), RecStored rd σ c (lvl + i) lvs[i] rs[i]) ∧
      ws'.folds.length = (lvs.getLastD default).foldsOff + (lvs.getLastD default).folds ∧
      (∀ j (h : j < ws'.folds.length), LoadHolds rd (σ (.n osFch)) j ws'.folds[j]) ∧
      ws'.quad = (osLevels c lvl lvs st).2.quad σ ∧
      ws'.target = σ (.n (osLevels c lvl lvs st).2.t) ∧
      (osLevels c lvl lvs st).2.fs.length = 5 ∧ PadOk σ (osLevels c lvl lvs st).2.pad ∧
      (osLevels c lvl lvs st).2.co ≤ 8 ∧
      (osLevels c lvl lvs st).2.cur σ = st.cur σ * gen ^ xs.length
  | [lv], [level], lvl, st, ws, R, root, hok, hcal, hin, hall => by
    obtain ⟨hcfg, hfold, h4, hml, hlen, hfin⟩ := hok
    have hall' : AllOk (coreProgram.Rel rd) rd σ (osLevel c lvl lv st).1 := by
      have := (allOk_append.mp hall).1
      exact this
    obtain ⟨xs, os, ws', ms, r, hrd, hrun, hmsl, hfm, hgl, hrec, hfl, hfch, hq, ht, hfs, hpad,
      hco, hcur⟩ := osLevel_final_sound hcal.1 hcfg hfold h4 hml hlen hfin hin hall'
    exact ⟨xs, os, R, ms, ws', [r], hrd, hrun, hmsl, hfm, by simpa using hgl, rfl,
      fun i hi _ ↦ by
        obtain rfl : i = 0 := by simpa using hi
        simpa using hrec, hfl, hfch, hq, ht, hfs, hpad, hco, hcur⟩
  | lv :: lv' :: lvs, level :: next :: cfg, lvl, st, ws, R, root, hok, hcal, hin, hall => by
    obtain ⟨hcfg, hfold, h4, hml, hm, hlvl, hnf, hoff', hshape, hrest⟩ := hok
    have e1 : osLevels c lvl (lv :: lv' :: lvs) st =
        ((osLevel c lvl lv st).1 ++ (osLevels c (lvl + 1) (lv' :: lvs) (osLevel c lvl lv st).2).1,
          (osLevels c (lvl + 1) (lv' :: lvs) (osLevel c lvl lv st).2).2) := rfl
    rw [e1] at hall ⊢
    rw [allOk_append] at hall
    obtain ⟨xs1, os1, ws1, root', r, hrd1, hrun1, hin1, hgl1, hrec1, hcur1⟩ :=
      osLevel_nonfinal_sound (rest := cfg) hcal.1 hcfg hfold h4 hml hm hlvl hnf hoff' hshape hin
        hall.1
    obtain ⟨xs2, os2, R', ms, ws', rs, hrd2, hrun2, hmsl, hfm, hgl2, hrl, hrec2, hfl, hfch, hq,
      ht, hfs, hpad, hco, hcur2⟩ :=
      osLevels_sound (lv' :: lvs) (next :: cfg) (lvl + 1) _ ws1 _ root' hrest hcal.2 hin1 hall.2
    refine ⟨xs1 ++ xs2, os1 ++ os2, R', ms, ws', r :: rs, readsAt_append hrd1 (by
        rw [← hcur1]; exact hrd2), ?_, hmsl, hfm, ?_, by simp [hrl], ?_, hfl, hfch, hq, ht, hfs,
      hpad, hco, ?_⟩
    · exact RunsWith.bind' hrun1 hrun2
    · rw [hgl2, hgl1]; simp
    · intro i hi hi'
      rcases i with _ | i
      · simpa using hrec1
      · have := hrec2 i (by simpa using hi) (by simpa using hi')
        rw [show lvl + 1 + i = lvl + (i + 1) by ring] at this
        simpa using this
    · rw [hcur2, hcur1, List.length_append, pow_add, mul_assoc]
  | [], _, _, _, _, _, _, hok, _, _, _ => by simp [LevelsOk] at hok
  | [_], [], _, _, _, _, _, hok, _, _, _ => by simp [LevelsOk] at hok
  | [_], _ :: _ :: _, _, _, _, _, _, hok, _, _, _ => by simp [LevelsOk] at hok
  | _ :: _ :: _, [], _, _, _, _, _, hok, _, _, _ => by simp [LevelsOk] at hok
  | _ :: _ :: _, [_], _, _, _, _, _, hok, _, _, _ => by simp [LevelsOk] at hok

end
end LeanVM.Guest.B1.Whir
