/-
  LeanVM.Guest.B1.Comp.Tables.VtAllC

  `verify_tables` complete over a completeness model, and the deployed completeness recovered at
  `CompModel.deployed`.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.VtBodyC
public import LeanVM.Guest.B1.Comp.Tables.DeployedC

/-!
# `verify_tables` at the deployed model

At `CompModel.deployed` the total hash is BLAKE2s and every hash of a run is answered, so
`vt_bodyC` gives the deployed `vt_body` (`vt_body_of_comp`), on which the deployed placed
completeness of `verify_tables` rests.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

section
variable {rd : Reader}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `verify_tables`' whole body, deployed (`vt_body`), from the model's. -/
theorem vt_body_of_comp {κ : ℕ} (hκ : 7 ≤ κ) (hlow : LowDef κ rd) {σ : Val}
    {cur zeta bk sq fpw pool cplen dims rowsP beta chiP bv mF bF m0 m1 m2 v0 v1 v2 : E}
    {point alphas : List E} {logMem : ℕ} {rowsN : List ℕ} {cv pi : Digest} {ptr : ℕ → E}
    {bytecode : List K} {cl : ℕ → E} {cvr : ℕ → Digest} {wsr : ℕ → List E} {ch : ℕ → E}
    {evss : List (List E)}
    (hcv : (σ (.n 0), σ (.n 1)) = digestScalars cv) (h2 : σ (.n 2) = cur) (h3 : σ (.n 3) = (digestScalars pi).1)
    (h4 : σ (.n 4) = (digestScalars pi).2) (h5 : σ (.n 5) = zeta)
    (h6 : σ (.n 6) = gen ^ point.length) (h7 : σ (.n 7) = dims) (h8 : σ (.n 8) = rowsP)
    (h9 : σ (.n 9) = bk) (h10 : σ (.n 10) = sq) (h11 : σ (.n 11) = fpw) (h12 : σ (.n 12) = beta)
    (h13 : σ (.n 13) = pool) (h14 : σ (.n 14) = cplen) (h15 : σ (.n 15) = chiP) (h16 : σ (.n 16) = v0)
    (h17 : σ (.n 17) = v1) (h18 : σ (.n 18) = v2)
    (hb : bytecode.length = 2 ^ 22) (hal : alphas.length = 4)
    (hrl : rowsN.length = 6) (hτ : ∀ t < 6, log2Ceil (rowsN.getD t 0) < 29)
    (hτp : ∀ t < 6, log2Ceil (rowsN.getD t 0) ≤ point.length) (hlm16 : 16 ≤ logMem) (h32 : logMem ≤ 32)
    (hlmp : logMem ≤ point.length) (h18p : 18 ≤ point.length) (hpl : point.length < 33)
    (hso1 : ∀ r < 37, LoadHolds rd (ptr 0) r (gen ^ (stackOrder ((List.range 37).map (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))))).getD r 0))
    (hso2 : ∀ r < 28, LoadHolds rd (ptr 0) (74 + r)
      (gen ^ (74 + (stackOrder ((List.range 28).map fun i => (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) (74 + i))).getD r 0)))
    (hside : ∀ b < 102, LoadHolds rd (ptr 1) b (word (vtBlockSide b) 0 0))
    (hbk : ∀ b < 102, LoadHolds rd bk b (gen ^ (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) b))
    (hsq : ∀ j < 34, LoadHolds rd sq j (gen ^ 2 ^ j))
    (hoff1 : ∀ i < 37, LoadHolds rd (ptr 2) i (gen ^ (stackOffsets ((List.range 37).map (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))))).1.getD i 0))
    (hoff2 : ∀ i < 28, LoadHolds rd (ptr 2) (74 + i)
      (gen ^ (stackOffsets ((List.range 28).map fun i => (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) (74 + i))).1.getD i 0))
    (hdims : ReadsAt rd dims (gen ^ logMem :: rowsN.map fun n ↦ gen ^ log2Ceil n))
    (hrows : ReadsAt rd rowsP (rowsN.map eOfNat)) (hz : ReadsAt rd zeta point)
    (hidx : ∀ t < 34, LoadHolds rd (ptr 3) t (1 + gen ^ 2 ^ t))
    (hm : ∀ i < 65, SelMem rd bk (ptr 2) point (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) (selOff (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)))) ptr i)
    (hfpwR : ReadsAt rd fpw (eqKernel alphas))
    (hpI2 : ReadsAt rd (ptr 11) (idxChainW point logMem))
    (hb1 : LoadHolds rd (ptr 4) 1 ((idxChainW point logMem).getD logMem 0))
    (hpI3 : ReadsAt rd (ptr 15) (idxChainW point 18)) (hb2 : LoadHolds rd (ptr 4) 2 ((idxChainW point 18).getD 18 0))
    (hcur : ReadsAt rd cur [m0, m1, m2, mF, bF]) (hpool : ReadsAt rd pool [m0, m1, m2, mF, bF])
    (hcpl : ∀ j < 4, LoadHolds rd cplen j (gen ^ logMem)) (hcpl4 : LoadHolds rd cplen 4 (gen ^ 18))
    (hcl0 : cl 0 = dot ((powers (challengeOf (sqCv (obsAll cv [m0, m1, m2, mF, bF]))) (vtNC + 3)).drop vtNC) (busVal (layoutOf bytecode logMem rowsN) alphas beta point [v0, v1, v2] [m0, m1, m2] mF bF bv).totals)
    (hcvr0 : cvr 0 = sqCv (obsAll cv [m0, m1, m2, mF, bF]))
    (hrnd : ∀ r < vtN (layoutOf bytecode logMem rowsN), RunsTo (roundPoly 4 (cl r) none) (cvr r) (wsr r) (cl (r + 1), ch r) (cvr (r + 1)))
    (hshape : evss.map List.length = vtEvalVars.map List.length) (hflat : evss.flatten.length = 104)
    (hfin : (ttVal ((powers (challengeOf (sqCv (obsAll cv [m0, m1, m2, mF, bF]))) (vtNC + 3)).take vtNC) ((powers (challengeOf (sqCv (obsAll cv [m0, m1, m2, mF, bF]))) (vtNC + 3)).drop vtNC)
      ((List.range (vtN (layoutOf bytecode logMem rowsN))).map ch).reverse (vtRows (layoutOf bytecode logMem rowsN) (busVal (layoutOf bytecode logMem rowsN) alphas beta point [v0, v1, v2] [m0, m1, m2] mF bF bv) ((List.range (vtN (layoutOf bytecode logMem rowsN))).map ch).reverse) evss 0 0 []).1 = cl (vtN (layoutOf bytecode logMem rowsN)))
    (hxs5 : ReadsAt rd (cur * gen ^ 5) ((List.range (vtN (layoutOf bytecode logMem rowsN))).flatMap wsr ++ evss.flatten))
    (hchi : ReadsAt rd chiP ((List.range (vtN (layoutOf bytecode logMem rowsN))).map ch).reverse)
    (hpR : ReadsAt rd (ptr 202) (zcRoundsW cvr cur cl (vtN (layoutOf bytecode logMem rowsN))))
    (hpC : ReadsAt rd (ptr 203) (zcCprodW ch (vtN (layoutOf bytecode logMem rowsN))))
    (hpP : ReadsAt rd (ptr 204) (zcPeqW point ((List.range (vtN (layoutOf bytecode logMem rowsN))).map ch).reverse (vtN (layoutOf bytecode logMem rowsN))))
    (hpoolE : ∀ j < 104, LoadHolds rd pool (5 + j) (evss.flatten.getD j 0))
    (h109 : LoadHolds rd pool 109 (ofK ((digestScalars pi).1.limb 0) +
      challengeOf (sqCv (obsAll (cvr (vtN (layoutOf bytecode logMem rowsN))) evss.flatten)) * (ofK ((digestScalars pi).1.limb 0) + ofK ((digestScalars pi).2.limb 0))))
    (h110 : LoadHolds rd pool 110 (ofK ((digestScalars pi).1.limb 1) +
      challengeOf (sqCv (obsAll (cvr (vtN (layoutOf bytecode logMem rowsN))) evss.flatten)) * (ofK ((digestScalars pi).1.limb 1) + ofK ((digestScalars pi).2.limb 1))))
    (h111 : LoadHolds rd pool 111 0)
    (hcplT : ∀ t < 6, ∀ j < evCnt.getD t 0, LoadHolds rd cplen (5 + (evFirst.getD t 0 + j))
      (gen ^ log2Ceil (rowsN.getD t 0))) :
    Completes (coreProgram.Rel rd) rd 19 8179 ((vtPre.drop 0).take ((((213 + (1225 + (67 + 69))) + ((3 + (28 + (11 + (28 + (80 + (28 + 56)))))) + ((2798 - 1808) + (28 + (571 + ((4206 - 3397) + (28 + (4273 - 4234)))))))) + (101 + (1 + (16 * 15 + ((4863 - 4615) + (16 * 15 + ((5392 - 5103) + (16 * 8 + ((5669 - 5520) + (16 * 15 + ((6192 - 5909) + (16 * 14 + ((6694 - 6416) + (16 * 37 + ((7854 - 7286)))))))))))))))) + 45)) σ
      (fun σ' => (∀ i < 65, SelPost point (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) (selOff (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)))) ptr i σ') ∧ σ' (.n 24) = ptr 0 ∧
        σ' (.n 25) = ptr 1 ∧ σ' (.n 128) = ptr 2 ∧ σ' (.n 1817) = ptr 3 ∧ σ' (.n 1852) = ptr 4 ∧
        σ' (.n 1925) = ptr 11 ∧ σ' (.n 2029) = ptr 15 ∧ σ' (.n 4636) = ptr 202 ∧ σ' (.n 4639) = ptr 203 ∧
        σ' (.n 4655) = ptr 204 ∧ σ' (.n 4554) = gen ^ vtN (layoutOf bytecode logMem rowsN) ∧
        σ' (.n 8171) = (digestScalars (sqCv (obsAll (cvr (vtN (layoutOf bytecode logMem rowsN))) evss.flatten))).1 ∧
        σ' (.n 8172) = (digestScalars (sqCv (obsAll (cvr (vtN (layoutOf bytecode logMem rowsN))) evss.flatten))).2 ∧
        σ' (.n 8175) = cur * gen ^ (5 + 3 * vtN (layoutOf bytecode logMem rowsN)) * gen ^ 104 ∧ σ' (.n 8176) = gen ^ vtN (layoutOf bytecode logMem rowsN) ∧
        σ' (.n 8177) = bv ∧ σ' (.n 8178) = challengeOf (sqCv (obsAll (cvr (vtN (layoutOf bytecode logMem rowsN))) evss.flatten))) := by
  have h := vt_bodyC (CM := CompModel.deployed) hκ hlow hcv h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    h13 h14 h15 h16 h17 h18 hb hal hrl hτ hτp hlm16 h32 hlmp h18p hpl hso1 hso2 hside hbk hsq
    hoff1 hoff2 hdims hrows hz hidx hm hfpwR hpI2 hb1 hpI3 hb2 hcur hpool hcpl hcpl4 hcl0 hcvr0
    (fun r hr => runsToM_hm_deployed.mpr (hrnd r hr)) hshape hflat hfin hxs5 hchi hpR hpC hpP
    hpoolE h109 h110 h111 hcplT
    (obsAns_hm_deployed _ _) rfl (obsAns_hm_deployed _ _) rfl
  exact h.toDeployed

end

end
end LeanVM.Guest.B1.VerifySub
