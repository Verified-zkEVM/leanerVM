/-
  LeanVM.Guest.B2C.ArmsFresh

  No table selector is a temporary of its function, so the checker's `keep` holds outright.
-/

module

public import LeanVM.Guest.B2C.KRetemp
public import LeanVM.Guest.Memory.GuestFresh

/-!
# The table selectors are not temporaries

The compiled functions with table jumps (`armsCheck`, by the kernel over `Data.plumbs`: at leanVM
`1a379148`, `verify_lean_xmss`, `sp_wots`, the `opening_queries` variants and their window loops)
have their selectors outside their temporaries: a function's temporaries are the freshness
certificates' list for the large functions (`temps19`, …, by `tmps19`, …; `bigTemps`), and computed
from its body for the others (`armTemps`). So `ArmsFresh` holds (`armsFresh`), and with it `keep`
(`kfacts_keep_all`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- Every arm `a` of the plumbs `l`, the first of index `k`, passes `q`. -/
def armsCheck (q : ℕ → ℕ × ℕ × ℕ → Bool) : List Plumb → ℕ → Bool
  | [], _ => true
  | p :: ps, k => p.arms.all (q k) && armsCheck q ps (k + 1)

theorem armsCheck_spec {q : ℕ → ℕ × ℕ × ℕ → Bool} : ∀ {l : List Plumb} {k : ℕ},
    armsCheck q l k = true → ∀ j, ∀ a ∈ (listElementOrDefault l j {}).arms, q (j + k) a = true
  | [], _, _, j, a, ha => by cases j <;> simp [listElementOrDefault] at ha
  | p :: ps, k, h, j, a, ha => by
    simp only [armsCheck, Bool.and_eq_true, List.all_eq_true] at h
    cases j with
    | zero => simpa using h.1 a ha
    | succ j =>
      have := armsCheck_spec h.2 j a ha
      rwa [show j + (k + 1) = j + 1 + k by omega] at this

/-- The large functions' temporaries, from the freshness certificates (`GuestFresh.Temps*`), by
compiled function index (core index `+ 1`). -/
def bigTemps : List (ℕ × List ℕ) :=
  [(20, temps19), (21, temps20), (538, temps537), (666, temps665), (677, temps676), (688, temps687),
   (699, temps698), (848, temps847), (856, temps855), (862, temps861), (868, temps867),
   (874, temps873), (880, temps879), (886, temps885), (888, temps887), (890, temps889),
   (894, temps893), (896, temps895), (898, temps897), (902, temps901), (906, temps905),
   (908, temps907), (912, temps911), (914, temps913), (916, temps915), (918, temps917),
   (919, temps918), (920, temps919), (921, temps920), (922, temps921), (923, temps922),
   (924, temps923), (926, temps925), (928, temps927), (930, temps929), (932, temps931),
   (933, temps932), (934, temps933), (935, temps934), (936, temps935), (937, temps936),
   (939, temps938), (941, temps940), (943, temps942), (945, temps944), (947, temps946)]

/-- The entry of index `j`, if any. -/
def tempsFind : List (ℕ × List ℕ) → ℕ → Option (List ℕ)
  | [], _ => none
  | (k, t) :: l, j => if j = k then some t else tempsFind l j

theorem tempsFind_ok {P : ℕ → List ℕ → Prop} : ∀ {l : List (ℕ × List ℕ)},
    (∀ p ∈ l, P p.1 p.2) → ∀ {j : ℕ} {t : List ℕ}, tempsFind l j = some t → P j t
  | [], _, _, _, h => by simp [tempsFind] at h
  | (k, s) :: l, hl, j, t, h => by
    unfold tempsFind at h
    split_ifs at h with hj
    · subst hj; cases h; exact hl _ List.mem_cons_self
    · exact tempsFind_ok (fun p hp ↦ hl p (List.mem_cons_of_mem _ hp)) h

set_option maxRecDepth 100000 in
theorem bigTemps_ok :
    ∀ p ∈ bigTemps, (Stmt.tmpsList (coreOf p.1).body).map V.idx = p.2 := by
  rw [← List.forall_iff_forall_mem]
  simp only [bigTemps, List.Forall]
  exact ⟨tmps19, tmps20, tmps537, tmps665, tmps676, tmps687, tmps698, tmps847, tmps855, tmps861,
    tmps867, tmps873, tmps879, tmps885, tmps887, tmps889, tmps893, tmps895, tmps897, tmps901,
    tmps905, tmps907, tmps911, tmps913, tmps915, tmps917, tmps918, tmps919, tmps920, tmps921,
    tmps922, tmps923, tmps925, tmps927, tmps929, tmps931, tmps932, tmps933, tmps934, tmps935,
    tmps936, tmps938, tmps940, tmps942, tmps944, tmps946⟩

/-- Compiled function `j`'s temporaries, by index. -/
noncomputable def armTemps (j : ℕ) : List ℕ :=
  (tempsFind bigTemps j).getD ((Stmt.tmpsList (coreOf j).body).map V.idx)

theorem armTemps_eq (j : ℕ) : (Stmt.tmpsList (coreOf j).body).map V.idx = armTemps j := by
  unfold armTemps
  cases h : tempsFind bigTemps j with
  | none => rfl
  | some t =>
    exact tempsFind_ok (P := fun j t ↦ (Stmt.tmpsList (coreOf j).body).map V.idx = t) bigTemps_ok h

/-- The arms' check: no arm's selector is a temporary of its function. -/
noncomputable def armOk (k : ℕ) (a : ℕ × ℕ × ℕ) : Bool := !(armTemps k).contains a.1

theorem armsCheck_plumbs : armsCheck armOk Data.plumbs 0 = true := by decide +kernel

private theorem not_tmp {body : List Stmt} {ts : List ℕ} (h : (Stmt.tmpsList body).map V.idx = ts)
    {x : ℕ} (hx : ts.contains x = false) : V.n x ∉ Stmt.tmpsList body := fun hm ↦ by
  have : x ∈ ts := h ▸ List.mem_map_of_mem (f := V.idx) hm
  simp [this] at hx

/-- **No table selector is a temporary of its function.** -/
theorem armsFresh : ArmsFresh := by
  intro j a ha
  have h := armsCheck_spec armsCheck_plumbs j a ha
  simp only [armOk, Nat.add_zero, Bool.not_eq_true'] at h
  exact not_tmp (armTemps_eq j) h

/-- **The checker's `keep`**, outright. -/
theorem kfacts_keep_all (hdr : E × E) (T : Tree) :
    ∀ ν, ∀ I ∈ honestInsts coreProgram fs H hdr T,
      ∀ I' ∈ honestInsts coreProgram fs H hdr (T.retemp coreProgram fs ν 0),
        I'.fp = I.fp → I'.t = I.t.retemp coreProgram fs ν I.fp → ∀ q ∈ I'.cells C,
          ¬ TmpOff coreProgram cert I.t q.1 → q ∈ I.cells C :=
  kfacts_keep coreProgram_fresh armsFresh hdr T

end
end LeanVM.Guest.B2C
