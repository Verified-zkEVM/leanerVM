import LeanVM.E2E.NoForgery
import LeanVM.E2E.Reduction.VerifyBound
import LeanVM.E2E.Deployed
import XmssSecurity

/-!
# Tests: T5, no forgery, and the game-to-cache bridge

* The end lemmas of T5 and the bridge rest on Lean's three axioms.
* **leanXMSS's multi-user security plugs in**: `aggregate_no_forgery` at
  `XmssSecurity.leanXmss_has_multi_user_security` and leanXMSS's verification bound
  (`verify_isTotalQueryBound`), leanSPHINCS's multi-user bound and the honest signers' costs left
  as hypotheses.
* Digests and the schemes' 256-bit outputs are in bijection.
* **The costs**: leanXMSS's and leanSPHINCS's key generation, signer and verification are
  query-bounded, at lean_xmss's exact key-generation count and lean_sphincs's `keygenCost + 1`;
  the closed form is one fraction; the instantiated theorem is `aggregate_no_forgery_closed` at
  the parameter set's constants.
-/

namespace LeanVMTests.E2E.NoForgery

open OracleComp OracleSpec LeanVM.E2E LeanVM.Node LeanVM.Protocol.Compile.Rom
open scoped ENNReal

/-- info: 'LeanVM.E2E.rel_idealVerify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.rel_idealVerify

/-- info: 'LeanVM.E2E.idealVerify_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.idealVerify_mono

/-- info: 'LeanVM.E2E.game_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.game_accepted

/-- info: 'LeanVM.E2E.prEvent_game_accepted_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_game_accepted_le

/-- info: 'LeanVM.E2E.aggregate_knowledge_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_knowledge_sub

/-- info: 'LeanVM.E2E.digestBits_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.digestBits_bijective

/-- info: 'LeanVM.E2E.evalDistEq_run_toW_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.evalDistEq_run_toW_nil

/-- info: 'LeanVM.E2E.gameRec_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.gameRec_map

/-- info: 'LeanVM.E2E.gameRec_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.gameRec_trace

/-- info: 'LeanVM.E2E.toW_gameCompRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.toW_gameCompRec

/-- info: 'LeanVM.E2E.romRun_bind_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.romRun_bind_comm

/-- info: 'LeanVM.E2E.romRun_sKeygenAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.romRun_sKeygenAll

/-- info: 'LeanVM.E2E.count_le_of_isQueryBoundP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.count_le_of_isQueryBoundP

/-- info: 'LeanVM.E2E.verify_isTotalQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.verify_isTotalQueryBound

/-- info: 'LeanVM.E2E.XmssRed.map_xPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.XmssRed.map_xPrefix

/-- info: 'LeanVM.E2E.XmssRed.xCore_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.XmssRed.xCore_log

/-- info: 'LeanVM.E2E.XmssRed.prEvent_forgedX_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.XmssRed.prEvent_forgedX_le

/-- info: 'LeanVM.E2E.XmssRed.hasHashQueryBound_xAdv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.XmssRed.hasHashQueryBound_xAdv

/-- info: 'LeanVM.E2E.SphincsRed.evalDistEq_sPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.SphincsRed.evalDistEq_sPrefix

/-- info: 'LeanVM.E2E.SphincsRed.sCore_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.SphincsRed.sCore_log

/-- info: 'LeanVM.E2E.SphincsRed.prEvent_forgedS_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.SphincsRed.prEvent_forgedS_le

/-- info: 'LeanVM.E2E.SphincsRed.hasHashQueryBound_sAdv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.SphincsRed.hasHashQueryBound_sAdv

/-- info: 'LeanVM.E2E.prEvent_breaks_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.prEvent_breaks_le

/-- info: 'LeanVM.E2E.aggregate_no_forgery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.aggregate_no_forgery

/-- info: 'LeanVM.E2E.keygenFromSeed_isTotalQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.keygenFromSeed_isTotalQueryBound

/-- info: 'LeanVM.E2E.sign_isTotalQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sign_isTotalQueryBound

/-- info: 'LeanVM.E2E.sphincsVerify_isTotalQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincsVerify_isTotalQueryBound

/-- info: 'LeanVM.E2E.sphincsKeygenFromSeed_isTotalQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincsKeygenFromSeed_isTotalQueryBound

/-- info: 'LeanVM.E2E.sphincsSign_isTotalQueryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincsSign_isTotalQueryBound

/-- info: 'LeanVM.E2E.sphincsSignBound_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincsSignBound_eq

/-- info: 'LeanVM.E2E.xmssKeygenBound_eq_keygenQueries' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.xmssKeygenBound_eq_keygenQueries

/-- info: 'LeanVM.E2E.sphincsKeygenBound_eq_keygenCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.sphincsKeygenBound_eq_keygenCost

/-- info: 'LeanVM.E2E.noForgeryError_eq_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.noForgeryError_eq_closed

/-- info: 'LeanVM.E2E.closedError_eq_num' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.closedError_eq_num

/-- info: 'LeanVM.E2E.closedError_one_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanVM.E2E.closedError_one_slot

/-- **The end theorem at leanXMSS's proved multi-user security** and its verification bound. -/
example [Sphincs.Params] {nx ns : ℕ} {εs : ℕ → ℝ≥0∞}
    (hsph : Sphincs.Security.Multi.HasMultiUserBound ns εs) {cxk csk cxs css cs : ℕ}
    (hxk : ∀ seed, IsTotalQueryBound (LeanXmss.Seeded.keygenFromSeed seed) cxk)
    (hsk : ∀ seed, IsTotalQueryBound (Sphincs.Seeded.keygenFromSeed seed) csk)
    (hxs : ∀ sk i msg, IsTotalQueryBound
      (LeanXmss.Seeded.sign sk i msg : OracleComp LeanXmss.HashSpec _) cxs)
    (hss : ∀ sk msg, IsTotalQueryBound
      (Sphincs.Seeded.sign sk msg : OracleComp Sphincs.HashSpec _) css)
    (hvs : ∀ pk msg σ, IsTotalQueryBound
      (Sphincs.Concrete.verify pk msg σ : OracleComp Sphincs.HashSpec Bool) cs)
    (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget + xmssVerifyBound < 2 ^ 126) :
    Pr{let z ← game LeanVM.Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      noForgeryError (nx * cxk + ns * csk + (qH + sX * cxs + sS * css) + budget) nx
        xmssVerifyBound cs εs :=
  aggregate_no_forgery XmssSecurity.leanXmss_has_multi_user_security hsph hxk hsk hxs hss
    verify_isTotalQueryBound hvs fuel budget A hH hX hS hq

/-- The proved costs' values. -/
example : xmssKeygenBound = 13434881 ∧ xmssSignBound = 2 ^ 33 + 40304605 ∧ xmssVerifyBound = 384 ∧
    sphincsVerifyBound = 686 :=
  ⟨xmssKeygenBound_eq, xmssSignBound_eq, rfl, rfl⟩

section Full

attribute [local instance] Sphincs.Lifetimes.full

/-- **The instantiated theorem is the closed one** at subtree height 26's constants. -/
example {nx ns : ℕ} (fuel budget : ℕ) (A : GameAdversary nx ns) {qH sX sS : ℕ}
    (hH : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvHash qH)
    (hX : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvXmss sX)
    (hS : ∀ pkx pks, IsQueryBoundP (A pkx pks) AdvSphincs sS)
    (hq : gameQueries nx ns qH sX sS budget + 384 < 2 ^ 126) :
    Pr{let z ← game LeanVM.Guest.guest fuel budget A}[Breaks z.1 z.2] ≤
      closedError (gameQueries nx ns qH sX sS budget) nx ns :=
  aggregate_no_forgery_closed XmssSecurity.leanXmss_has_multi_user_security
    (Sphincs.Lifetimes.full_multiUserKey ns) (multiBound_le ns _ _ _ _) fuel budget A hH hX hS hq

/-- leanSPHINCS's costs at subtree height 26. -/
example : sphincsKeygenBound = 15166603265 ∧ sphincsSignBound = 23756655991 :=
  ⟨sphincsKeygenBound_full, sphincsSignBound_full⟩

end Full

/-- A digest's 256 bits read back. -/
example (d : LeanVM.Protocol.Digest) : bitsD (hBits d) = d := bitsD_hBits d

end LeanVMTests.E2E.NoForgery
