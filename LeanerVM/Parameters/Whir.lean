/-
  LeanerVM.Parameters.Whir

  leanVM's WHIR parameters: the fold factors, the rate schedule, the residual size, the grinding
  budget, the stacking window, the tabulated query counts, and the ladder of levels an opening of
  a given size and rate runs.
-/

module

public import Mathlib.Data.Rat.Init

/-!
# WHIR parameters

Category B. The constants are transcribed from `crates/pcs/src/whir_config.rs:38-86` of the
pinned leanVM (`a386121f84292f6fa663aaa3e570c15bc0240ea2`), the ladder geometry from its
`derive_ladder` and `derive_ladder_shape` (`:260-311`), the stacking window from
`crates/lean_vm/src/pcs.rs:49-51`, and the query counts from the second verifier,
`python-verifier/verifier.py:900-935` (`WHIR_QUERIES`, `derive_config`). The specification
describes the protocol these parameters instantiate (Annex B, Protocol B.1,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`) and gives no numbers.

An opening of a stack of `2^μ` elements of `K` at rate `2^-R` runs a *ladder* of levels. Level 0
folds `initialFold = 6` variables; every later level folds `subsequentFold = 4`, or what remains,
until at most `residualMaxLog = 5` variables remain, which are sent in the clear. The rate
exponent of a level is the previous one plus the previous fold minus a domain reduction,
`initialReduction = 3` after level 0 and `subsequentReduction = 1` after every later level. Each
level opens `queries` positions after `queryGrindingBits = 17` bits of grinding; from level 1 on,
one out-of-domain sample binds the level's commitment (`oodSamples`).

The query counts are the Rust's *output*, not its derivation: `optimize_johnson_level`
(`whir_config.rs:639-707`) minimises the queries of each level subject to the 128-bit
round-by-round targets of Annex B's Theorem B.2 under a floating-point MCA formula, and this
module does not restate that search. The table is the one the Python verifier carries, indexed
by rate exponent `1..4` and stack size `15..28`; outside that window `ladder` is `none`, as both
verifiers reject (`validate_log_inv_rate`, `whir_config.rs:48-56`; `verifier.py:923`).

The search's other output, the Johnson slack `η_i` of each level (the radius is
`γ_i = 1 - √ρ_i - η_i`), is read by no verifier but fixes the constants of the opening's soundness.
`slackTable` holds it as the bits of the Rust's double, dumped from the pinned Rust by
`scripts/dump-whir-eta-rust.sh`, and `slacks` as the exact rational each double denotes
(`ofDoubleBits`). The Rust rounds `⌈√ρ/η⌉` in doubles; nothing here does, the soundness side
computes from the exact rational.

The Rust API takes the witness size as `m = μ + LOG_PACKING` bits, `LOG_PACKING = 6`
(`crates/pcs/src/pack.rs:7`); `ladder` takes the stack size `μ`, as the Python `derive_config`
does. `LOG_INV_RATE_0 = 1` (`whir_config.rs:41`) is the rate the Rust test suite proves at, not a
verifier parameter: the rate exponent is announced with the sizes.
-/

namespace LeanerVM.Parameters.Whir

@[expose] public section

/-! ## Constants (`whir_config.rs`) -/

/-- Variables folded at level 0: the lane fold (`INITIAL_FOLDING_FACTOR`, `whir_config.rs:67`). -/
def initialFold : ℕ := 6

/-- Variables folded at every later level (`SUBSEQUENT_FOLDING_FACTOR`, `whir_config.rs:68`). -/
def subsequentFold : ℕ := 4

/-- Bits the Reed–Solomon domain shrinks by after level 0, so that the rate exponent rises by
`initialFold - initialReduction` (`RS_DOMAIN_INITIAL_REDUCTION_FACTOR`, `whir_config.rs:73`). -/
def initialReduction : ℕ := 3

/-- Bits the domain shrinks by after every later level (`RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR`,
`whir_config.rs:78`). -/
def subsequentReduction : ℕ := 1

/-- Folding stops once at most this many variables remain; the residual multilinear is sent in
the clear (`RESIDUAL_MAX_LOG`, `whir_config.rs:86`). -/
def residualMaxLog : ℕ := 5

/-- Grinding bits before each level's query positions are sampled (`QUERY_GRINDING_BITS`,
`whir_config.rs:60`). -/
def queryGrindingBits : ℕ := 17

/-- The round-by-round security target the query counts were derived for, in bits
(`SECURITY_BITS`, `whir_config.rs:38`). -/
def securityBits : ℕ := 128

/-- The smallest stack the PCS commits: `MIN_MU` (`pcs.rs:49`; `MIN_STACKED_LOG`,
`verifier.py:907`). A smaller witness is padded up to it. -/
def minLogStack : ℕ := 15

/-- The largest stack the PCS commits: `MAX_MU` (`pcs.rs:51`; `MAX_STACKED_LOG`,
`verifier.py:908`). -/
def maxLogStack : ℕ := 28

/-- The smallest rate exponent of level 0 (`MIN_LOG_INV_RATE`, `whir_config.rs:44`). -/
def minLogInvRate : ℕ := 1

/-- The largest rate exponent of level 0 (`MAX_LOG_INV_RATE`, `whir_config.rs:45`). -/
def maxLogInvRate : ℕ := 4

/-- Out-of-domain samples taken after a level's commitment: none at level 0, whose commitment the
opening's own evaluation claim binds, and one at every later level (`whir_config.rs:108-115`).
The Rust derives the count at each later level as the fewest samples `s ∈ 1..8` whose
out-of-domain bits `s·(192 − log μ) − (2 log L − 1)` clear 128 (`optimize_johnson_level`,
`whir_config.rs:677-685`), and its production test fixes the result at one for stack sizes 22
to 28 (`whir_config.rs:1021, 1033`); the second verifier takes one sample per level after the
first (`verifier.py:1033-1037`). `scripts/whir-mca-budget.py`, which reproduces the Rust's
search at its `η`, finds one sample at all 168 later levels of the window, one sample giving
between 150.4 and 172.4 bits. -/
def oodSamples (level : ℕ) : ℕ := if level = 0 then 0 else 1

/-! ## The ladder -/

/-- One level of an opening: the number of sumcheck rounds it folds (`ℓ_i`), the rate exponent
of the code its commitment is in (`R_i`), and the number of positions queried (`t_i`), in the
notation of Annex B. The Johnson slack `η_i` the query count was optimised for is not a field:
no verifier reads it; the soundness of the opening reads it from `slacks`. -/
structure Level where
  fold : ℕ
  logInvRate : ℕ
  queries : ℕ
  deriving DecidableEq

/-- The levels after the first, as pairs (fold, rate exponent): while more than `residualMaxLog`
variables remain, fold `subsequentFold` of them (or all that remain) at the rate exponent the
previous level's fold and the pending domain reduction give (`derive_ladder`,
`whir_config.rs:260-299`, with `derive_ladder_shape`'s rate rule, `:302-311`). `fuel` bounds the
recursion; every level folds at least one variable, so `remaining` fuel is enough. -/
def levelsFrom : (fuel remaining prevFold prevRate reduction : ℕ) → List (ℕ × ℕ)
  | 0, _, _, _, _ => []
  | fuel + 1, remaining, prevFold, prevRate, reduction =>
    if remaining ≤ residualMaxLog then []
    else
      let rate := prevRate + prevFold - reduction
      let fold := min subsequentFold remaining
      (fold, rate) :: levelsFrom fuel (remaining - fold) fold rate subsequentReduction

/-- The ladder geometry of a `μ`-variable stack at rate exponent `logInvRate`: level 0 folds
`initialFold` at that rate, then `levelsFrom` (`derive_config`, `verifier.py:920-935`). -/
def shape (μ logInvRate : ℕ) : List (ℕ × ℕ) :=
  (initialFold, logInvRate) ::
    levelsFrom μ (μ - initialFold) initialFold logInvRate initialReduction

/-- The variables left after every fold: the size of the residual sent in the clear. -/
def residualLog (μ logInvRate : ℕ) : ℕ := μ - ((shape μ logInvRate).map Prod.fst).sum

/-- The query counts `WHIR_QUERIES` of `verifier.py:910`, verbatim: row `R - 1` for the rate
exponent `R`, entry `μ - 15` for the stack size `μ`, one count per level. -/
def queryTable : List (List (List ℕ)) := [
  [[223, 55], [223, 56, 30], [223, 56, 31], [224, 56, 32], [224, 56, 32], [224, 56, 32, 22],
   [224, 56, 32, 22], [225, 56, 32, 23], [225, 56, 32, 23], [225, 56, 32, 23, 17],
   [226, 56, 32, 23, 17], [226, 56, 32, 23, 18], [227, 56, 32, 23, 18],
   [228, 56, 32, 23, 18, 14]],
  [[112, 45], [112, 45, 27], [112, 45, 28], [112, 45, 28], [112, 45, 28], [112, 45, 28, 20],
   [112, 45, 28, 20], [112, 45, 28, 21], [112, 45, 28, 21], [113, 45, 28, 21, 16],
   [113, 45, 28, 21, 16], [113, 45, 28, 21, 16], [113, 45, 28, 21, 16],
   [113, 45, 28, 21, 17, 13]],
  [[75, 37], [75, 37, 24], [75, 38, 25], [75, 38, 25], [75, 38, 25], [75, 38, 25, 18],
   [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19, 15],
   [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15],
   [76, 38, 25, 19, 16, 13]],
  [[56, 32], [56, 32, 22], [56, 32, 22], [56, 32, 23], [56, 32, 23], [56, 32, 23, 17],
   [56, 32, 23, 17], [56, 32, 23, 18], [56, 32, 23, 18], [57, 32, 23, 18, 14],
   [57, 32, 23, 18, 14], [57, 32, 23, 18, 15], [57, 33, 23, 18, 15],
   [57, 33, 23, 18, 15, 12]]]

/-- The window the parameters are defined on: the stacking window and the rate range
(`verifier.py:923`; `cpu/mod.rs:130-178` checks the stack, `whir_config.rs:48-56` the rate). -/
def Admissible (μ logInvRate : ℕ) : Prop :=
  minLogStack ≤ μ ∧ μ ≤ maxLogStack ∧ minLogInvRate ≤ logInvRate ∧ logInvRate ≤ maxLogInvRate

instance {μ logInvRate : ℕ} : Decidable (Admissible μ logInvRate) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The ladder of an admissible stack size and rate: the geometry of `shape` paired with the
tabulated query counts, level by level. `none` outside the window, and `none` if the table did
not have one count per level (`verifier.py:934`), so that no level is silently dropped. -/
def ladder (μ logInvRate : ℕ) : Option (List Level) :=
  if Admissible μ logInvRate then
    let geometry := shape μ logInvRate
    let queries := (queryTable.getD (logInvRate - minLogInvRate) []).getD (μ - minLogStack) []
    if geometry.length = queries.length then
      some (List.zipWith (fun (g : ℕ × ℕ) q ↦ ⟨g.1, g.2, q⟩) geometry queries)
    else none
  else none

/-! ## The Johnson slacks -/

/-- The value of a positive normal IEEE-754 double below `2 ^ 53` from its bits: the significand
`2 ^ 52 + f` over `2 ^ (1075 - e)`, with `e` the biased exponent and `f` the fraction (the bits
below `2 ^ 52`). -/
def ofDoubleBits (b : ℕ) : ℚ :=
  ((2 ^ 52 + b % 2 ^ 52 : ℕ) : ℚ) / ((2 ^ (1075 - b / 2 ^ 52) : ℕ) : ℚ)

/-- The Johnson slack `η_i` of every level, as the bits of the Rust's double: row `R - 1` for the
rate exponent `R`, entry `μ - 15` for the stack size `μ`, one per level. Dumped from the pinned
leanVM by `scripts/dump-whir-eta-rust.sh`, verbatim: the slack `optimize_johnson_level` chooses
(`whir_config.rs:639-707`) and `WhirSecurityConfig::derive_config_with_log_inv_rate` stores in
each level (`whir_config.rs:919-975`). -/
def slackTable : List (List (List ℕ)) := [
  [[4565890337769909851, 4560555982262904673],
   [4564294581683613527, 4572486138701581144, 4555989971039431741],
   [4563506416833593714, 4571356616720724013, 4561428200397571798],
   [4567388474562172082, 4570365476108201193, 4571843123429225431],
   [4567289569872359857, 4569825056222356870, 4569576046677342970],
   [4567241508367534738, 4569533335456744002, 4568093808460250043, 4569080167745471525],
   [4567209939137705885, 4569441612369742871, 4567351857424099131, 4562457373416891434],
   [4569694870621521228, 4569351302267109375, 4566989546295220044, 4571633555397909190],
   [4569694899416949997, 4569351742112031539, 4566773934421244721, 4571715933429013222],
   [4569694913814623188, 4569263004746669675, 4566673313921436159, 4571082975990281567,
    4563158583445365038],
   [4571651481273994601, 4569263113342896292, 4566501948517600593, 4571118368419734486,
    4557301372457746772],
   [4571651483658880136, 4569263167640388189, 4566503030416074268, 4571136012381503263,
    4568313230291019151],
   [4572873216197310759, 4569263194788978789, 4566503571315773629, 4571144821388864505,
    4568415167903744451],
   [4574061281398221826, 4569263208363235252, 4566503841753241587, 4571149222660275904,
    4568465520081121143, 4559379593968814626]],
  [[4570373530057788614, 4574365401079753102],
   [4569828811973961264, 4572969119708491639, 4570466916789303341],
   [4569582809592518943, 4572136831910809448, 4572777631903800466],
   [4569442503276486551, 4571735302111035919, 4569898585350664386],
   [4569351742112031539, 4571497891757897706, 4567820243154682359],
   [4569307207120709161, 4571500262934172634, 4566758837217393284, 4567049320789799636],
   [4569307316391446503, 4571388624228779426, 4565845744858642101, 4559289109526345904],
   [4569307371026189902, 4571389202918660694, 4565417603314242116, 4570368832879254719],
   [4569307398343405288, 4571389492237104539, 4565026124529753896, 4570504749696221785],
   [4573680017919423763, 4571389636889703679, 4564845063006112717, 4570571885932724041,
    4563883193596185122],
   [4573680024623772547, 4571389709214347731, 4564846822869329494, 4569396849705372471,
    4560628524077270650],
   [4573680027975944542, 4571389745376255899, 4564847702639738879, 4569411108179673841,
    4558506105226892028],
   [4573680029652029940, 4571389763457106521, 4564848142484661043, 4569418226932634591,
    4556979477509450829],
   [4573680030490072489, 4571389772497505967, 4564848362397053645, 4569421783697046983,
    4568104124835625194, 4553538521907688148]],
  [[4572727948224638765, 4566648887388418001],
   [4572470311090270572, 4562146143298248993, 4567337726570004764],
   [4572389737343236430, 4575094206523962509, 4571945757539738718],
   [4572310710289628590, 4574640768691630335, 4569194202828834394],
   [4572311055864436516, 4574648598920395884, 4568046418175660216],
   [4572311228643929933, 4574652511161650460, 4567201700570159404, 4555767475869621725],
   [4572311315031699217, 4574654466565224658, 4566760330731168826, 4567763398130586843],
   [4572311358225089529, 4574655444087901752, 4566486788042164518, 4567129955770538694],
   [4572311379821661106, 4574655932804481934, 4566495454350116735, 4566508167630769938],
   [4572311390619915999, 4574656177151584825, 4566130744264798909, 4565586425978025613,
    4561964440145848394],
   [4572311396019035723, 4574656299322339769, 4566132818283489816, 4565617885915317097,
    4559948025910786023],
   [4572311398718593654, 4574656360407018153, 4566133855102860421, 4565633569436889343,
    4558072669483336818],
   [4572311400068372137, 4574656390949182578, 4566134373465072309, 4565641399665654892,
    4556993950814110297],
   [4576661990138480988, 4574656406220221099, 4566134632634312436, 4565645311906909468,
    4566068286305353545, 4558339532185940764]],
  [[4569825056222356870, 4569576046677342970],
   [4569533335456744002, 4568093808460250043, 4569080167745471525],
   [4569441612369742871, 4567351857424099131, 4562457373416891434],
   [4569351302267109375, 4566989546295220044, 4571633555397909190],
   [4569351742112031539, 4566773934421244721, 4571715933429013222],
   [4569263004746669675, 4566673313921436159, 4571082975990281567, 4563158583445365038],
   [4569263113342896292, 4566501948517600593, 4571118368419734486, 4557301372457746772],
   [4569263167640388189, 4566503030416074268, 4571136012381503263, 4568313230291019151],
   [4569263194788978789, 4566503571315773629, 4571144821388864505, 4568415167903744451],
   [4576491211158745543, 4566503841753241587, 4571149222660275904, 4568465520081121143,
    4559379593968814626],
   [4576491216249084435, 4566503976968880466, 4571151422489296876, 4568490546307989968,
    4556124924449900154],
   [4576491218794252061, 4566504044575926172, 4571152522202308607, 4568503022473003667,
    4563456945017205905],
   [4576491220066835418, 4575785641691217391, 4571153072008461312, 4568509251381844323,
    4563553052720160609],
   [4576491220703126983, 4575785650526153212, 4571153346898952064, 4568512363550705166,
    4563600525208254698, 4555989971039431741]]]

/-- The Johnson slacks of the ladder of an admissible stack size and rate, one per level, the
exact rationals of the Rust's doubles. `none` outside the window. -/
def slacks (μ logInvRate : ℕ) : Option (List ℚ) :=
  if Admissible μ logInvRate then
    some (((slackTable.getD (logInvRate - minLogInvRate) []).getD (μ - minLogStack) []).map
      ofDoubleBits)
  else none

/-- The log block lengths `κ_i + R_i` of the levels' codes: the message log after a level's fold
plus its rate exponent (`LevelShapes.block_len`, `whir_config.rs:124-159`). -/
def blockLogs (μ : ℕ) : List Level → List ℕ
  | [] => []
  | l :: rest => (μ - l.fold + l.logInvRate) :: blockLogs (μ - l.fold) rest

/-! ## Structure of the table

Each fact below is decided over the 56 admissible pairs; the general statement follows by
bounding the quantifiers. -/

@[elab_as_elim]
private theorem of_window {P : ℕ → ℕ → Prop}
    (key : ∀ μ < maxLogStack + 1, ∀ r < maxLogInvRate + 1, Admissible μ r → P μ r)
    {μ logInvRate : ℕ} (h : Admissible μ logInvRate) : P μ logInvRate :=
  key μ (Nat.lt_succ_of_le h.2.1) logInvRate (Nat.lt_succ_of_le h.2.2.2) h

/-- The table has one query count per level of the geometry: `ladder` is defined on the whole
window. -/
theorem ladder_isSome {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    (ladder μ logInvRate).isSome :=
  of_window (by decide +kernel) h

/-- Every ladder has at least two levels (`whir_config.rs:291-293`). -/
theorem ladder_length {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    ∀ levels, ladder μ logInvRate = some levels → 2 ≤ levels.length :=
  of_window (by decide +kernel) h

/-- The residual is at most `residualMaxLog` variables. -/
theorem residualLog_le {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    residualLog μ logInvRate ≤ residualMaxLog :=
  of_window (by decide +kernel) h

/-- Every level's code fits the encoders: its log block length is at most 63, the bound of the
Rust's NTT (`additive_ntt_f64.rs:66`) and below Annex B's `κ_i + R_i ≤ 64`, and its query count
is at most its block length (`whir_config.rs:673`). -/
theorem ladder_blocks {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    ∀ levels, ladder μ logInvRate = some levels →
      ∀ p ∈ List.zip (blockLogs μ levels) levels, p.1 ≤ 63 ∧ p.2.queries ≤ 2 ^ p.1 := by
  intro levels hl p hp
  have key := of_window (P := fun μ r ↦ ∀ levels, ladder μ r = some levels →
    (List.zip (blockLogs μ levels) levels).all (fun p ↦ p.1 ≤ 63 ∧ p.2.queries ≤ 2 ^ p.1))
    (by decide +kernel) h
  exact of_decide_eq_true (List.all_eq_true.mp (key levels hl) p hp)

/-- The slack table has one slack per level of every ladder. -/
theorem slacks_length {μ logInvRate : ℕ} (h : Admissible μ logInvRate) :
    (slacks μ logInvRate).map List.length = (ladder μ logInvRate).map List.length :=
  of_window (by decide +kernel) h

end
end LeanerVM.Parameters.Whir
