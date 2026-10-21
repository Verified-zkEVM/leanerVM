/-
  LeanVM.Guest.Memory.StaticSoundB

  The soundness of the static weight checker (`StaticSound.lean`) under any semantics of
  `BLAKE2S`.
-/

module

public import LeanVM.Guest.Memory.StaticSound
public import LeanVM.Guest.Memory.RestrictB
public import LeanVM.Guest.Memory.SizeB

/-!
# The static weight checker under any `BLAKE2S` semantics

The checker (`Static.lean`) reads code, not semantics, so its soundness holds over the trees
valid under any `S : BlakeSem`: `StaticSound.lean`'s `HoldsAll`, `KB` and lemmas with `S` a
parameter (`HoldsAllB`, `KBB`, `chkB_sound`, `weightB_le_of_stat`, `weightLeB_of_stat`,
`weightB_le_of_loop`, `costB_le_of_stat`, …).

* `holdsAllB_deployed`, `kBB_deployed`: at `blakeDeployed`, they are `StaticSound.lean`'s.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {S : BlakeSem}

/-! ## Blocks -/

section Block

variable {P : Core.Program} {rd : Reader} {σ : Val} {cert : String → Cert} {ω : String → ℕ}
  {α : Bool}

variable (S) in
/-- Every event holds. -/
def HoldsAllB (rd : Reader) (σ : Val) (es : List Ev) : Prop := ∀ e ∈ es, e.HoldsB S rd σ

variable (P α rd σ cert ω) in
variable (S) in
/-- **The callees of a path cost at most `X`, with its `HeapBuf`s**, every callee satisfying its
certificate. -/
def KBB (es : List Ev) (X : ℕ) : Prop :=
  ∀ kids, Tree.KidsValidB S P rd σ (calls es) kids → Tree.BufsOkKids P kids →
    (∀ k ∈ kids, ∀ args' rets', k.ValidB S P rd args' rets' → k.BufsOk P → Bound P α cert ω k args') →
      Tree.costKids P α ω kids + aw α σ es ≤ X

theorem kidsValidB_split : ∀ {cs cs' : List Call} {ks : List Tree},
    Tree.KidsValidB S P rd σ (cs ++ cs') ks →
      ∃ ks₁ ks₂, ks = ks₁ ++ ks₂ ∧ Tree.KidsValidB S P rd σ cs ks₁ ∧ Tree.KidsValidB S P rd σ cs' ks₂
  | [], _, ks, h => ⟨[], ks, rfl, by simp [Tree.KidsValidB], h⟩
  | c :: cs, cs', [], h => h.elim
  | c :: cs, cs', k :: ks, ⟨hn, hc, h⟩ => by
      obtain ⟨ks₁, ks₂, rfl, h1, h2⟩ := kidsValidB_split h
      exact ⟨k :: ks₁, ks₂, rfl, ⟨hn, hc, h1⟩, h2⟩

theorem KBB_mono {es : List Ev} {X Y : ℕ} (h : KBB S P rd σ cert ω α es X) (hXY : X ≤ Y) :
    KBB S P rd σ cert ω α es Y := fun kids hk ho hb => (h kids hk ho hb).trans hXY

theorem KBB_nil (X : ℕ) : KBB S P rd σ cert ω α [] X := fun kids hk _ _ => by
  cases kids with
  | nil => rw [Tree.costKids, aw_nil]; omega
  | cons _ _ => exact hk.elim

theorem KBB_append {es es' : List Ev} {X Y : ℕ} (h : KBB S P rd σ cert ω α es X)
    (h' : KBB S P rd σ cert ω α es' Y) : KBB S P rd σ cert ω α (es ++ es') (X + Y) := fun kids hk ho hb => by
  rw [calls_append] at hk
  obtain ⟨ks₁, ks₂, rfl, h1, h2⟩ := kidsValidB_split hk
  obtain ⟨ho1, ho2⟩ := bufsOkKids_split ks₁ ks₂ ho
  rw [costKids_append, aw_append]
  have := Nat.add_le_add (h ks₁ h1 ho1 fun k hk' => hb k (List.mem_append_left _ hk'))
    (h' ks₂ h2 ho2 fun k hk' => hb k (List.mem_append_right _ hk'))
  omega

theorem KBB_nocall {es : List Ev} (hc : calls es = []) (ha : aw α σ es = 0) (X : ℕ) :
    KBB S P rd σ cert ω α es X := by
  intro kids hk ho hb
  rw [hc] at hk
  have := KBB_nil (P := P) (α := α) (rd := rd) (σ := σ) (cert := cert) (ω := ω) X kids
    (by simpa [calls] using hk) ho hb
  rw [aw_nil] at this
  rw [ha]
  exact this

theorem KBB_seq {o k : Out} {X Y : ℕ} (hh : HoldsAllB S rd σ (o.seq k).evs)
    (h1 : HoldsAllB S rd σ o.evs → KBB S P rd σ cert ω α o.evs X)
    (h2 : ∀ es, o = .fall es → HoldsAllB S rd σ es → HoldsAllB S rd σ k.evs → KBB S P rd σ cert ω α k.evs Y) :
    KBB S P rd σ cert ω α (o.seq k).evs (X + Y) := by
  cases o with
  | fall es =>
      cases k with
      | fall es' =>
          simp only [Out.seq, Out.pre, Out.evs] at hh ⊢
          have ha : HoldsAllB S rd σ es := fun e he => hh e (List.mem_append_left _ he)
          have hb : HoldsAllB S rd σ es' := fun e he => hh e (List.mem_append_right _ he)
          exact KBB_append (h1 ha) (h2 es rfl ha hb)
      | ret es' vs =>
          simp only [Out.seq, Out.pre, Out.evs] at hh ⊢
          have ha : HoldsAllB S rd σ es := fun e he => hh e (List.mem_append_left _ he)
          have hb : HoldsAllB S rd σ es' := fun e he => hh e (List.mem_append_right _ he)
          exact KBB_append (h1 ha) (h2 es rfl ha hb)
      | stuck => simp only [Out.seq, Out.pre, Out.evs]; exact KBB_nil _
  | ret es vs =>
      simp only [Out.seq, Out.evs] at hh ⊢
      exact KBB_mono (h1 hh) (Nat.le_add_right _ _)
  | stuck => simp only [Out.seq, Out.evs]; exact KBB_nil _

theorem KBB_pre {o : Out} {c : V} {X : ℕ} (hh : HoldsAllB S rd σ (o.pre [.inK c]).evs)
    (h : HoldsAllB S rd σ o.evs → KBB S P rd σ cert ω α o.evs X) : KBB S P rd σ cert ω α (o.pre [.inK c]).evs X := by
  cases o with
  | fall es =>
      simp only [Out.pre, Out.evs, List.singleton_append] at hh ⊢
      have := h fun e he => hh e (List.mem_cons_of_mem _ he)
      intro kids hk ho hb
      rw [aw_cons_none rfl]
      exact this kids (by simpa [calls, Ev.call?, Out.evs, List.filterMap_cons] using hk) ho hb
  | ret es vs =>
      simp only [Out.pre, Out.evs, List.singleton_append] at hh ⊢
      have := h fun e he => hh e (List.mem_cons_of_mem _ he)
      intro kids hk ho hb
      rw [aw_cons_none rfl]
      exact this kids (by simpa [calls, Ev.call?, Out.evs, List.filterMap_cons] using hk) ho hb
  | stuck => simp only [Out.pre, Out.evs]; exact KBB_nil _

/-- A call site's callee: its bound bounds the callee of one frame. -/
theorem KBB_site {ρ : Env} {ps : List V} {args : List E} (hρ : EnvOk σ ρ) (hp : ps.map σ = args)
    {g : String} {a r : List V} {t : Bool} {R : Acc} (h : siteB cert ρ ps g a = some R)
    (hr : ArgsPre R.2 args) {es : List Ev} (hc : calls es = [⟨g, a, r, t⟩]) (ha : aw α σ es = 0)
    {Y : ℕ} (hY : t = false → (if α then ω g else 0) ≤ Y) :
    KBB S P rd σ cert ω α es (R.1.eval args + Y) := by
  intro kids hk ho hb
  rw [hc] at hk
  rw [ha]
  match kids, hk with
  | [k], ⟨hn, hkv, _⟩ =>
      rw [Tree.costKids, Tree.costKids]
      simp only at hn hkv
      simp only [Tree.BufsOkKids] at ho
      by_cases ht : t = true
      · rw [ite_eq_left ht] at hkv
        have := siteB_sound hρ hp h hr hn (hb k List.mem_cons_self _ _ hkv ho.1)
        omega
      · rw [ite_eq_right ht] at hkv
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hkv
        simp only [Tree.name] at hn
        subst hn
        have := hY (by simpa using ht)
        rw [Tree.cost]
        omega

variable {ks : List (V × ℕ)} {ps : List V} {self : String} {args : List E} {wl : String → Option ℕ}

/-- **An atom's bound bounds its `HeapBuf`**, and keeps the constants and the bounds true. -/
theorem atomBB_sound {ρ ρ' : Env × BEnv} {a : Atom} {r : Acc} (hρ : Env2Ok σ args ρ)
    (hp : ps.map σ = args) (h : atomB α ks ps ρ a = some (r, ρ')) (hh : (Ev.atom a).HoldsB S rd σ) :
    Env2Ok σ args ρ' ∧ r.2 = [] ∧ aw α σ [.atom a] ≤ r.1.eval args := by
  cases a with
  | const v w =>
      simp only [atomB] at h
      have ha : aw α σ [.atom (.const v w)] = 0 := by rw [aw_cons_none rfl, aw_nil]
      rw [ha]
      split at h
      · rename_i e he
        split at h
        · rename_i hok
          cases h
          obtain ⟨hw, he20⟩ := constOk_spec hok
          have hv : σ v = w := hh
          refine ⟨⟨fun q hq => ?_, hρ.2⟩, rfl, Nat.zero_le _⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨hv.trans hw, by omega⟩
          · exact hρ.1 q hq
        · cases h; exact ⟨hρ, rfl, Nat.zero_le _⟩
      · cases h; exact ⟨hρ, rfl, Nat.zero_le _⟩
  | mul d x y =>
      simp only [atomB] at h
      have ha : aw α σ [.atom (.mul d x y)] = 0 := by rw [aw_cons_none rfl, aw_nil]
      rw [ha]
      split at h
      · split at h
        · rename_i b c hb hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨⟨hρ.1, fun q hq => ?_⟩, rfl, Nat.zero_le _⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · have hd : σ d = σ x * σ y := hh
            obtain ⟨hy, -⟩ := cls_pow hρ.1 hc
            rw [hd, hy]
            have := bnd_sound hρ hp hb
            simp only [Aff.eval_add, Aff.eval_mk_nil]
            exact (logG_mul_le _ _).trans (by omega)
          · exact hρ.2 q hq
        · cases h
      · cases h; exact ⟨hρ, rfl, Nat.zero_le _⟩
  | hint hn =>
      cases hn with
      | alloc d n =>
          simp only [atomB, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨hρ, by split_ifs <;> rfl, ?_⟩
          cases α <;> simp [aw, allocs, Ev.alloc?, Acc.zero, Aff.eval]
      | allocDyn d sz =>
          cases α with
          | false =>
              simp only [atomB, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨hρ, rfl, by simp [aw]⟩
          | true =>
              simp only [atomB, ↓reduceIte] at h
              split at h
              · rename_i b hb
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨hρ, rfl, ?_⟩
                simpa [aw, allocs, Ev.alloc?] using bnd_sound hρ hp hb
              · cases h
      | _ =>
          simp only [atomB, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hρ, rfl, by rw [aw_cons_none rfl, aw_nil]; exact Nat.zero_le _⟩
  | _ =>
      simp only [atomB, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hρ, rfl, by rw [aw_cons_none rfl, aw_nil]; exact Nat.zero_le _⟩

mutual
/-- **A block's bound bounds its path's callees.** -/
theorem blockBB_sound (hp : ps.map σ = args) (hwl : WlOk wl ω) : ∀ (ss : List Stmt) (ρ : Env × BEnv) (r : Acc),
    Env2Ok σ args ρ →
    blockB cert wl α ks ps self ρ ss = some r → ArgsPre r.2 args → HoldsAllB S rd σ (walk σ ss).evs →
      KBB S P rd σ cert ω α (walk σ ss).evs (r.1.eval args)
  | [], _, _, _, _, _, _ => by rw [walk]; exact KBB_nil _
  | s :: ss, ρ, r, hρ, h, hr, hh => by
      rw [walk] at hh ⊢
      cases s with
      | atom a =>
          simp only [blockB] at h
          split at h
          · rename_i r1 ρ' hab
            obtain ⟨r2, rr, h2, hrr, rfl⟩ := addAcc_some h
            cases h2
            simp only [Acc.add, argsPre_append] at hr
            simp only [Acc.add, Aff.eval_add]
            refine KBB_seq hh (fun h1 => ?_) fun es he h1 h2 => ?_
            · simp only [walk1, Out.evs] at h1 ⊢
              obtain ⟨-, -, hw⟩ := atomBB_sound hρ hp hab (h1 _ List.mem_cons_self)
              intro kids hk _ hb
              cases kids with
              | nil => rw [Tree.costKids]; omega
              | cons _ _ => rw [show calls [Ev.atom a] = [] from rfl] at hk; exact hk.elim
            · simp only [walk1, Out.fall.injEq] at he
              subst he
              obtain ⟨hρ', -, -⟩ := atomBB_sound hρ hp hab (h1 _ List.mem_cons_self)
              exact blockBB_sound hp hwl ss ρ' rr hρ' hrr hr.2 h2
          · cases h
      | ite c z n =>
          simp only [blockB] at h
          obtain ⟨rzn, rr, hzn, hrr, rfl⟩ := addAcc_some h
          obtain ⟨rz, rn, hz, hn, rfl⟩ := maxAcc_some hzn
          simp only [Acc.add, Acc.join, argsPre_append] at hr
          simp only [Acc.add, Aff.eval_add]
          refine KBB_seq hh (fun h1 => ?_) fun es _ _ h2 => blockBB_sound hp hwl ss ρ rr hρ hrr hr.2 h2
          rw [walk1] at h1 ⊢
          refine KBB_pre h1 fun h1' => ?_
          split_ifs
          · rw [ite_eq_left (by assumption)] at h1'
            exact KBB_mono (blockBB_sound hp hwl z ρ rz hρ hz hr.1.1 h1') (join_eval_left _ _ _)
          · rw [ite_eq_right (by assumption)] at h1'
            exact KBB_mono (blockBB_sound hp hwl n ρ rn hρ hn hr.1.2 h1') (join_eval_right _ _ _)
      | match_ x arms =>
          simp only [blockB] at h
          obtain ⟨ra, rr, ha, hrr, rfl⟩ := addAcc_some h
          simp only [Acc.add, argsPre_append] at hr
          simp only [Acc.add, Aff.eval_add]
          refine KBB_seq hh (fun h1 => ?_) fun es _ _ h2 => blockBB_sound hp hwl ss ρ rr hρ hrr hr.2 h2
          rw [walk1] at h1 ⊢
          exact armsBB_sound hp hwl x arms 0 ρ ra hρ ha hr.1 h1
      | call g a r' =>
          simp only [blockB] at h
          obtain ⟨rs, rr, hs, hrr, rfl⟩ := addAcc_some h
          simp only [Acc.add, argsPre_append] at hr
          simp only [Acc.add, Aff.eval_add]
          refine KBB_seq hh (fun _ => KBB_mono (KBB_site hρ.1 hp hs hr.1 (t := true) (r := r') ?_ ?_
            (Y := 0) fun h => absurd h (by decide)) (by omega))
            fun es _ _ h2 => blockBB_sound hp hwl ss ρ rr hρ hrr hr.2 h2
          · simp [walk1, Out.evs, calls, Ev.call?]
          · simp only [walk1, Out.evs]; rw [aw_cons_none rfl, aw_nil]
      | callIf c g a =>
          simp only [blockB] at h
          split at h
          · cases h
          · obtain ⟨rs, rpr, hs, hpr, rfl⟩ := addAcc_some h
            obtain ⟨rph, rr, hph, hrr, rfl⟩ := addAcc_some hpr
            simp only [Acc.add, argsPre_append] at hr
            simp only [Acc.add, Aff.eval_add]
            rw [← Nat.add_assoc]
            refine KBB_seq hh (fun _ => ?_) fun es _ _ h2 => blockBB_sound hp hwl ss ρ rr hρ hrr hr.2.2 h2
            have hY := phB_sound (args := args) hwl hph
            by_cases h0 : σ c = 0
            · exact KBB_site hρ.1 hp hs hr.1 (t := false) (r := []) (by
                simp only [walk1, Out.evs, h0, ↓reduceIte]; rfl)
                (by simp only [walk1, Out.evs, h0, ↓reduceIte]; rw [aw_cons_none rfl, aw_cons_none rfl, aw_nil])
                fun _ => hY
            · exact KBB_site hρ.1 hp hs hr.1 (t := true) (r := []) (by
                simp only [walk1, Out.evs, h0, ↓reduceIte]; rfl)
                (by simp only [walk1, Out.evs, h0, ↓reduceIte]; rw [aw_cons_none rfl, aw_cons_none rfl, aw_nil])
                fun h => absurd h (by decide)
      | dispatch x gs a r' =>
          simp only [blockB] at h
          obtain ⟨rs, rr, hs, hrr, rfl⟩ := addAcc_some h
          simp only [Acc.add, argsPre_append] at hr
          simp only [Acc.add, Aff.eval_add]
          refine KBB_seq hh (fun _ => ?_) fun es _ _ h2 => blockBB_sound hp hwl ss ρ rr hρ hrr hr.2 h2
          rw [walk1]
          rcases pick_cases (σ := σ) (x := x) (a := a) (r := r') gs 0 with hpk | ⟨g, hg, hpk⟩
          · rw [hpk]; exact KBB_nil _
          · rw [hpk]
            obtain ⟨Rg, h1, h2, h3⟩ := maxB_mem (args := args) hs g hg
            exact KBB_mono (KBB_site hρ.1 hp h1 (h3 hr.1) (t := true) (r := r')
              (by simp [Out.evs, calls, Ev.call?]) (by simp only [Out.evs]; rw [aw_cons_none rfl, aw_nil])
              (Y := 0) fun h => absurd h (by decide)) (by omega)
      | ret vs =>
          simp only [walk1, Out.seq, Out.evs]
          exact KBB_nil _

/-- `blockBB_sound` for the arms of a `match`. -/
theorem armsBB_sound (hp : ps.map σ = args) (hwl : WlOk wl ω) (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ)
    (ρ : Env × BEnv) (r : Acc), Env2Ok σ args ρ → armsB cert wl α ks ps self ρ arms = some r → ArgsPre r.2 args →
      HoldsAllB S rd σ (walkArms σ x j arms).evs → KBB S P rd σ cert ω α (walkArms σ x j arms).evs (r.1.eval args)
  | [], _, _, _, _, _, _, _ => by rw [walkArms]; exact KBB_nil _
  | a :: as, j, ρ, r, hρ, h, hr, hh => by
      simp only [armsB] at h
      obtain ⟨ra, rs, ha, hs, rfl⟩ := maxAcc_some h
      simp only [Acc.join, argsPre_append] at hr
      unfold walkArms at hh ⊢
      split_ifs at hh ⊢
      · exact KBB_mono (blockBB_sound hp hwl a ρ ra hρ ha hr.1 hh) (join_eval_left _ _ _)
      · exact KBB_mono (armsBB_sound hp hwl x as (j + 1) ρ rs hρ hs hr.2 hh) (join_eval_right _ _ _)
end

end Block

/-! ## Loop helpers -/

section Loop

variable {σ : Val}

variable {rd : Reader} {pre : List Stmt} {es : List Ev}

/-- A defining atom of a block without `ret`, on its path, holds. -/
theorem defAtomB_holds (hn : Stmt.noRetListS pre = true) (hw : walk σ pre = .fall es)
    (hh : HoldsAllB S rd σ es) {d : V} {a : Atom} (h : defAtom d pre = some a) : a.HoldsB S rd σ :=
  hh _ (atom_on_path hn hw (defAtom_mem h))

theorem isGB_val (hn : Stmt.noRetListS pre = true) (hw : walk σ pre = .fall es) (hh : HoldsAllB S rd σ es)
    {z : V} (h : (match defAtom z pre with
      | some (.const _ w) => constOk w 1
      | _ => false) = true) : σ z = ofK (gpow 1) := by
  split at h
  · rename_i x w hd
    have := defAtomB_holds hn hw hh hd
    rw [← defAtom_const hd]
    exact this.trans (constOk_spec h).1
  · cases h

theorem isStepB_val (hn : Stmt.noRetListS pre = true) (hw : walk σ pre = .fall es)
    (hh : HoldsAllB S rd σ es) {p d : V} (h : isStep pre p d = true) : σ d = σ p * ofK (gpow 1) := by
  unfold isStep at h
  split at h
  · rename_i x y z hd
    have hm : σ x = σ y * σ z := defAtomB_holds hn hw hh hd
    rw [← defAtom_mul hd, hm]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, hz⟩ | ⟨rfl, hz⟩
    · rw [isGB_val hn hw hh hz]
    · rw [isGB_val hn hw hh hz, mul_comm]
  · cases h

theorem isEndB_val (hn : Stmt.noRetListS pre = true) (hw : walk σ pre = .fall es)
    (hh : HoldsAllB S rd σ es) {p1 : Option V} {endc : Option ℕ} {y : V} (h : isEnd pre p1 endc y = true) :
    (endc = none → p1 = some y) ∧ ∀ e, endc = some e → σ y = ofK (gpow e) := by
  unfold isEnd at h
  cases endc with
  | none => exact ⟨fun _ => (by simpa using h), fun _ he => (by cases he)⟩
  | some e =>
      refine ⟨fun he => (by cases he), fun e' he => ?_⟩
      cases he
      simp only at h
      split at h
      · rename_i x w hd
        have := defAtomB_holds hn hw hh hd
        rw [← defAtom_const hd]
        exact this.trans (constOk_spec h).1
      · cases h

end Loop

/-! ## The main induction -/

section Main

variable {P : Core.Program} {α : Bool} {cert : String → Cert} {ω : String → ℕ} {rd : Reader}

/-- **Soundness of the static checker**: if every function of the program passes, every valid
tree satisfies its certificate. -/
theorem chkB_sound {X : String → Prop} (hchk : CheckedExcept P α cert ω X)
    (hX : ∀ f, X f → ∀ (t : Tree) (args rets : List E), t.name = f → t.ValidB S P rd args rets →
      t.BufsOk P → Bound P α cert ω t args) :
    ∀ (n : ℕ) (t : Tree) (args rets : List E), t.count ≤ n → t.ValidB S P rd args rets → t.BufsOk P →
      Bound P α cert ω t args
  | 0, t, _, _, hc, _, _ => by have := count_pos t; omega
  | _ + 1, .phantom .., _, _, _, hv, _ => hv.elim
  | n + 1, .node f σ bufs kids, args, rets, hc, hv, hbo => by
      by_cases hXf : X f
      · exact hX f hXf _ args rets rfl hv hbo
      have hbk : Tree.BufsOkKids P kids := by simp only [Tree.BufsOk] at hbo; exact hbo.2
      obtain ⟨fn, hf, hp, es, vs, hw, hr, hes, hk⟩ := hv
      have hcost : (Tree.node f σ bufs kids).cost P α ω = ω f + aw α σ es + Tree.costKids P α ω kids := by
        rw [Tree.cost]
        simp only [Tree.events, Tree.name, Tree.val, hf, hw, aw]
      have hname := fn_name_of_find hf
      obtain ⟨look, wl, hlook, hwl, hc'⟩ := hchk fn (List.mem_of_find?_eq_some hf) (by rw [hname]; exact hXf)
      have hIH : ∀ k ∈ kids, ∀ args' rets', k.ValidB S P rd args' rets' → k.BufsOk P →
          Bound P α cert ω k args' :=
        fun k hk' a' r' hv' hb' => chkB_sound hchk hX n k a' r' (by
          have := countKids_le hk'; rw [Tree.count] at hc; omega) hv' hb'
      unfold Bound
      simp only [Tree.name]
      unfold chkFn at hc'
      rw [hname] at hc'
      cases hcf : cert f with
      | none => trivial
      | stat pre b ks =>
          rw [hcf] at hc'
          simp only at hc'
          split at hc'
          · rename_i r hb
            simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc'
            intro hpre
            have hpr : ArgsPre r.2 args := fun q hq => hpre q (hc'.2 q hq)
            rw [blockR_eq] at hb
            replace hb := blockB_mono hlook _ _ hb
            have hkb := blockBB_sound (rd := rd) (ω := ω) hp hwl fn.body ([], []) r
              ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
              hb hpr (by rw [hw]; exact hes) kids (by rw [hw]; exact hk) hbk hIH
            rw [hw] at hkb
            simp only [Out.evs] at hkb
            rw [hcost]
            have := Aff.eval_le_of_leB hc'.1 args
            simp only [Aff.eval] at this hkb ⊢
            omega
          · cases hc'
      | loop endc pre b ks =>
          rw [hcf] at hc'
          simp only at hc'
          split at hc'
          · rename_i pre' hsh
            split at hc'
            · rename_i r hb
              simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc'
              obtain ⟨⟨⟨hle, hpre⟩, hbc⟩, hpc⟩ := hc'
              obtain ⟨c, i', p0, prest, hps, hbody, hnr, hst, x, y, hadd, hxy⟩ := loopShape_spec hsh
              rw [blockR_eq] at hb
              replace hb := blockB_mono hlook _ _ hb
              rw [hname] at hbody
              rw [hbody, walk_append] at hw
              rcases walk_noRet (σ := σ) pre' hnr with ⟨es1, hw1⟩ | hw1
              · rw [hw1] at hw
                have hwt : walk σ [.callIf c f (i' :: prest), .ret []] =
                    .ret [.inK c, if σ c = 0 then .skip f (i' :: prest) else .call f (i' :: prest) []] [] := by
                  simp [walk, walk1, Out.seq, Out.pre]
                rw [hwt] at hw
                simp only [Out.seq, Out.pre, Out.ret.injEq] at hw
                obtain ⟨rfl, rfl⟩ := hw
                have hes1 : HoldsAllB S rd σ es1 := fun e he => hes e (List.mem_append_left _ he)
                rw [calls_append] at hk
                obtain ⟨ks1, ks2, rfl, hk1, hk2⟩ := kidsValidB_split hk
                obtain ⟨hbk1, hbk2⟩ := bufsOkKids_split ks1 ks2 hbk
                intro a0 e h0 hend hae hord hpre0
                have hkb := blockBB_sound (rd := rd) (ω := ω) hp hwl pre' ([], []) r
                  ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩ hb (fun q hq => hpre0 q (hpre q hq))
                  (by rw [hw1]; exact hes1) ks1 (by rw [hw1]; exact hk1) hbk1
                  (fun k hk' => hIH k (List.mem_append_left _ hk'))
                have hle' := Aff.eval_le_of_leB hle args
                simp only [Aff.eval] at hle' hkb
                have hcalls : calls [Ev.inK c, if σ c = 0 then .skip f (i' :: prest)
                    else .call f (i' :: prest) []] = [⟨f, i' :: prest, [], !decide (σ c = 0)⟩] := by
                  by_cases h0c : σ c = 0 <;> simp only [h0c, ↓reduceIte, decide_true, decide_false,
                    Bool.not_true, Bool.not_false] <;> rfl
                rw [hcalls] at hk2
                have hargs : args = σ p0 :: prest.map σ := by rw [← hp, hps, List.map_cons]
                have hp0 : σ p0 = ofK (gpow a0) := by rw [← h0, hargs]; rfl
                have hi' : σ i' = ofK (gpow (a0 + 1)) := by
                  rw [isStepB_val hnr hw1 hes1 hst, hp0, ← ofK_mulS, gpow_succ']
                have hM : 1 ≤ e - a0 := by omega
                match ks2, hk2 with
                | [tk], ⟨htn, htv, _⟩ =>
                  have htail : aw α σ [Ev.inK c, if σ c = 0 then .skip f (i' :: prest)
                      else .call f (i' :: prest) []] = 0 := by
                    unfold aw allocs; split_ifs <;> rfl
                  rw [hw1] at hkb
                  simp only [Out.evs] at hkb
                  rw [hcost, aw_append, htail, costKids_append, Tree.costKids, Tree.costKids]
                  by_cases h0c : σ c = 0
                  · simp only [h0c, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at htv
                    obtain ⟨⟨g', σ', rfl⟩, -⟩ := htv
                    simp only [Tree.name] at htn
                    subst htn
                    simp only [Tree.cost, Aff.eval] at hkb hle' ⊢
                    have : b.eval args ≤ (e - a0) * b.eval args := Nat.le_mul_of_pos_left _ hM
                    simp only [Aff.eval] at this
                    omega
                  · simp only [h0c, decide_false, Bool.not_false, ↓reduceIte] at htv
                    have hb' := hIH tk (List.mem_append_right _ List.mem_cons_self) _ _ htv
                      (by simp only [Tree.BufsOkKids] at hbk2; exact hbk2.1)
                    unfold Bound at hb'
                    rw [htn, hcf] at hb'
                    simp only at hb'
                    have hargs'' : (i' :: prest).map σ = σ i' :: prest.map σ := rfl
                    have hget : ∀ k, k ≠ 0 → ((i' :: prest).map σ).getD k 0 = args.getD k 0 := by
                      intro k hk0
                      rw [hargs'', hargs]
                      cases k with
                      | zero => exact absurd rfl hk0
                      | succ k => simp
                    have hendeq : endOf endc ((i' :: prest).map σ) = endOf endc args := by
                      cases endc with
                      | some _ => rfl
                      | none => exact hget 1 (by omega)
                    have hyv : ∀ {z : V}, isEnd pre' prest.head? endc z = true → σ z = ofK (gpow e) := by
                      intro z hz
                      obtain ⟨h1, h2⟩ := isEndB_val hnr hw1 hes1 hz
                      cases endc with
                      | some e' => rw [h2 e' rfl]; exact hend
                      | none =>
                          have := h1 rfl
                          cases prest with
                          | nil => cases this
                          | cons y' ys =>
                              simp only [List.head?_cons, Option.some.injEq] at this
                              subst this
                              rw [← hend]
                              simp [endOf, hargs]
                    have hcv : σ c = σ x + σ y := defAtomB_holds hnr hw1 hes1 hadd
                    have hne : a0 + 1 ≠ e := by
                      intro hae'
                      apply h0c
                      rw [hcv, e_add_eq_zero_iff]
                      rcases hxy with ⟨hsx, hey⟩ | ⟨hsy, hex⟩
                      · rw [isStepB_val hnr hw1 hes1 hsx, hp0, ← ofK_mulS, gpow_succ', hyv hey, hae']
                      · rw [isStepB_val hnr hw1 hes1 hsy, hp0, ← ofK_mulS, gpow_succ', hyv hex, hae']
                    have hpre'' : ArgsPre pre ((i' :: prest).map σ) := by
                      intro q hq
                      rw [hget q.1 (hpc q hq)]
                      exact hpre0 q hq
                    have hbev : b.eval ((i' :: prest).map σ) = b.eval args := by
                      unfold Aff.eval
                      congr 1
                      congr 1
                      refine List.map_congr_left fun q hq => ?_
                      unfold argExp
                      rw [hget q.1 (hbc q hq)]
                    have htk := hb' (a0 + 1) e (by rw [hargs'']; simpa using hi') (by rw [hendeq]; exact hend)
                      (by omega) hord hpre''
                    rw [hbev] at htk
                    have he1 : e - a0 = (e - (a0 + 1)) + 1 := by omega
                    rw [he1, Nat.add_mul, Nat.one_mul]
                    simp only [Aff.eval] at htk ⊢
                    omega
              · rw [hw1] at hw; simp [Out.seq] at hw
            · cases hc'
          · cases hc'

/-- **A checked bound**: every valid tree of a function with a `stat` certificate costs at most
its bound, under its preconditions, the functions of `X` satisfying theirs by hypothesis. -/
theorem costB_le_of_stat {X : String → Prop} (hchk : CheckedExcept P α cert ω X)
    (hX : ∀ f, X f → ∀ (t : Tree) (args rets : List E), t.name = f → t.ValidB S P rd args rets →
      t.BufsOk P → Bound P α cert ω t args) {f : String}
    {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} (hcf : cert f = .stat pre b ks)
    {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.ValidB S P rd args rets) (hb : t.BufsOk P)
    (hpre : ArgsPre pre args) : t.cost P α ω ≤ b.eval args := by
  have := chkB_sound hchk hX t.count t args rets le_rfl hv hb
  unfold Bound at this
  rw [hn, hcf] at this
  exact this hpre

/-- **A checked loop**: a valid tree of a loop helper started at `g^a`, its end `g^e`, `a < e`,
costs at most `e - a` times its iteration's bound. -/
theorem costB_le_of_loop {X : String → Prop} (hchk : CheckedExcept P α cert ω X)
    (hX : ∀ f, X f → ∀ (t : Tree) (args rets : List E), t.name = f → t.ValidB S P rd args rets →
      t.BufsOk P → Bound P α cert ω t args) {f : String}
    {endc : Option ℕ} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : cert f = .loop endc pre b ks) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.ValidB S P rd args rets) (hb : t.BufsOk P) {a e : ℕ} (ha : args.getD 0 0 = ofK (gpow a))
    (he : endOf endc args = ofK (gpow e)) (hae : a < e) (heo : e < 2 ^ 64 - 1)
    (hpre : ArgsPre pre args) : t.cost P α ω ≤ (e - a) * b.eval args := by
  have := chkB_sound hchk hX t.count t args rets le_rfl hv hb
  unfold Bound at this
  rw [hn, hcf] at this
  exact this a e ha he hae heo hpre

theorem noHandB : ∀ f, (fun _ => False) f → ∀ (t : Tree) (args rets : List E), t.name = f →
    t.ValidB S P rd args rets → t.BufsOk P → Bound P α cert ω t args :=
  fun _ h => h.elim

/-- `costB_le_of_stat` for the weight. -/
theorem weightB_le_of_stat (hchk : Checked P false cert ω) {f : String}
    {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} (hcf : cert f = .stat pre b ks)
    {t : Tree} {args rets : List E} (hn : t.name = f) (hv : t.ValidB S P rd args rets) (hb : t.BufsOk P)
    (hpre : ArgsPre pre args) : t.weight ω ≤ b.eval args := by
  rw [← cost_false (P := P)]; exact costB_le_of_stat hchk noHandB hcf hn hv hb hpre

/-- **A constant checked bound** is a `WeightLeB`. -/
theorem weightLeB_of_stat (hchk : Checked P false cert ω) {f : String} {B : ℕ}
    {ks : List (V × ℕ)} (hcf : cert f = .stat [] ⟨B, []⟩ ks) : WeightLeB S P ω f fun _ => B :=
  fun _ _ _ _ hn hv hb => by
    have := weightB_le_of_stat hchk hcf hn hv hb (fun _ h => (List.not_mem_nil h).elim)
    simpa [Aff.eval] using this

/-- `costB_le_of_loop` for the weight. -/
theorem weightB_le_of_loop (hchk : Checked P false cert ω) {f : String}
    {endc : Option ℕ} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)}
    (hcf : cert f = .loop endc pre b ks) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.ValidB S P rd args rets) (hb : t.BufsOk P) {a e : ℕ} (ha : args.getD 0 0 = ofK (gpow a))
    (he : endOf endc args = ofK (gpow e)) (hae : a < e) (heo : e < 2 ^ 64 - 1)
    (hpre : ArgsPre pre args) : t.weight ω ≤ (e - a) * b.eval args := by
  rw [← cost_false (P := P)]; exact costB_le_of_loop hchk noHandB hcf hn hv hb ha he hae heo hpre

end Main

/-! ## At the deployed semantics -/

section Deployed

variable {P : Core.Program} {rd : Reader} {σ : Val}

/-- At the deployed semantics, `HoldsAllB` is `StaticSound.lean`'s `HoldsAll`. -/
theorem holdsAllB_deployed (es : List Ev) : HoldsAllB blakeDeployed rd σ es = HoldsAll rd σ es := by
  simp only [HoldsAllB, HoldsAll, ev_holdsB_deployed]

/-- At the deployed semantics, `KBB` is `StaticSound.lean`'s `KB`. -/
theorem kBB_deployed (cert : String → Cert) (ω : String → ℕ) (α : Bool) (es : List Ev) (X : ℕ) :
    KBB blakeDeployed P rd σ cert ω α es X = KB P rd σ cert ω α es X := by
  simp only [KBB, KB, kidsValidB_deployed, validB_deployed]

end Deployed

end
end LeanVM.Guest.Memory
