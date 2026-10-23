/-
  LeanVM.Guest.CertName

  The certificate of a guest function by its name.
-/

module

public import LeanVM.Guest.Glob
public import LeanVM.Guest.CoreNames
public import LeanVM.Guest.CheckSound

/-!
# Certificates by name

The located call relation (`Check.RL`) reads a callee's values off its frame through the callee's
certificate, which it finds by the callee's name: `certByName f` is the certificate of the first
function of `coreProgram` named `f`, and, the names being distinct (`coreProgram_names_nodup`),
`certByName (coreOf j).name = certOf j` (`certByName_coreOf`).
-/

namespace LeanVM.Guest

open LeanVM.Guest.Check

@[expose] public section

/-- The certificate of the function named `f`: `certOf` at its index in `coreProgram`, plus one
(`main` is function `1`). -/
noncomputable def certByName (f : String) : Cert :=
  certOf (coreProgram.findIdx (fun g ↦ g.name == f) + 1)

theorem findIdx_name_of_nodup :
    ∀ {l : List Core.Fn}, (l.map (·.name)).Nodup → ∀ {i : ℕ} (h : i < l.length),
      l.findIdx (fun g ↦ g.name == l[i].name) = i
  | [], _, _, h => absurd h (by simp)
  | g :: l, hn, i, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    cases i with
    | zero => simp [List.findIdx_cons]
    | succ i =>
      have hi : i < l.length := by simpa using h
      have hne : (g.name == l[i].name) = false := by
        rw [beq_eq_false_iff_ne]
        intro he
        exact hn.1 (he ▸ List.mem_map_of_mem (List.getElem_mem hi))
      rw [List.findIdx_cons, List.getElem_cons_succ, hne, findIdx_name_of_nodup hn.2 hi]
      rfl

theorem certByName_coreOf {j : ℕ} (h1 : 1 ≤ j) (h2 : j < nFns) :
    certByName (coreOf j).name = certOf j := by
  have hl : j - 1 < coreProgram.length := by
    have : coreProgram.length = 899 := coreProgram_length
    simp only [nFns] at h2
    omega
  unfold certByName coreOf
  rw [nth_eq hl, findIdx_name_of_nodup coreProgram_names_nodup hl]
  congr 1
  omega

end
end LeanVM.Guest
