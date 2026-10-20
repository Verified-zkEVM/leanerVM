import XmssSecurity.Proof.ConsistentQueryBound

open OracleComp OracleSpec ENNReal
namespace XmssSecurity.Security
set_option backward.isDefEq.respectTransparency false

def embed (adversary : Adversary) : XmssSecurity.Adversary :=
  ⟨adversary.main⟩

theorem game_embed (adversary : Adversary) :
    XmssSecurity.gameCore Seeded.scheme (embed adversary) = gameCore adversary := by
  unfold XmssSecurity.gameCore Seeded.gameRest
  change (Seeded.keygen >>= _) = _
  unfold Seeded.keygen gameCore
  simp only [bind_assoc]
  rfl

theorem experiment_embed (adversary : Adversary) :
    (simulateQ countedRomImpl (XmssSecurity.gameCore Seeded.scheme (embed adversary))).run.run' ∅ =
      experiment adversary := by
  rw [game_embed]
  rfl

theorem advantage_embed (adversary : Adversary) :
    XmssSecurity.forgeAdvantage Seeded.scheme (embed adversary) = forgeAdvantage adversary := by
  unfold forgeAdvantage XmssSecurity.forgeAdvantage
  rw [← experiment_embed, ← simulateQ_countHashQueries]
  have h := congrArg (fun computation : OracleComp OracleWorld Bool =>
    (simulateQ romImpl computation).run' ∅)
    (countHashQueries_forget (XmssSecurity.gameCore Seeded.scheme (embed adversary)))
  simp only [simulateQ_map, StateT.run'_map'] at h
  rw [← h]
  simpa only [probEvent_eq_eq_probOutput, Function.comp_def] using probEvent_map (mx := (simulateQ romImpl
    (countHashQueries (XmssSecurity.gameCore Seeded.scheme (embed adversary)))).run' ∅)
    (f := Prod.fst) (q := fun result => result = true)

end XmssSecurity.Security
