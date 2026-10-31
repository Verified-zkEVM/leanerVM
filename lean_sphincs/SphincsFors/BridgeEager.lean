import SphincsFors.BridgeInternalize
import Mathlib.Data.Set.Finite.List

/-! A computation whose hash queries are all short sees the lazy random oracle exactly as a
uniformly sampled table on the finite set of short inputs. Private draws stay private draws. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.Eager

open Completeness Internalize Short

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

abbrev ShortIn := {input : HashInput // IsShort input}

instance : Finite ShortIn := (List.finite_length_le UInt8 bound).to_subtype

noncomputable instance : Fintype ShortIn := Fintype.ofFinite _

noncomputable instance : DecidableEq ShortIn := Classical.decEq _

abbrev Table := ShortIn → HashOutput

noncomputable instance : SampleableType Table := SampleableType.ofFintype Table

/-- Cached answers take priority; short inputs fall back to the sampled table. -/
noncomputable def extend (cache : QueryCache HashSpec) (table : Table) : HashInput → HashOutput :=
  fun input => (cache input).getD (if h : IsShort input then table ⟨input, h⟩ else 0)

/-- Private draws are forwarded; hash queries read a fixed answer function. -/
noncomputable def fixedRom (answers : HashInput → HashOutput) : QueryImpl OracleWorld ProbComp
  | .inl draw => liftM (unifSpec.query draw)
  | .inr input => pure (answers input)

theorem extend_cacheQuery (cache : QueryCache HashSpec) (table : Table) {input : HashInput}
    (h : IsShort input) (hnone : cache input = none) (answer : HashOutput) :
    extend (cache.cacheQuery input answer) table =
      extend cache (Function.update table ⟨input, h⟩ answer) := by
  funext query
  by_cases hq : query = input
  · subst query
    simp [extend, h, QueryCache.cacheQuery_self, hnone]
  · simp only [extend, QueryCache.cacheQuery_of_ne _ _ hq]
    split
    · rename_i hshort
      rw [Function.update_of_ne (fun heq => hq (congrArg Subtype.val heq))]
    · rfl

theorem evalDist_map_bind' {α β γ : Type} (x : ProbComp α) (f : α → β) (g : β → ProbComp γ) :
    ((f <$> x) >>= g) =ᵈ (x >>= fun a => g (f a)) := by
  rw [bind_map_left]

end SphincsFors.Security.Eager
