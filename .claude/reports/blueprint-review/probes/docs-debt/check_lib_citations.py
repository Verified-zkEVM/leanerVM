#!/usr/bin/env python3
"""Probe (read-only): the blueprint's citations into the pinned libraries
(docs/roadmap/protocol-blueprint.md:234-251, 273-279, 290-295). For each (file, cited lines,
declaration names) report where the declaration actually is in the pinned sources under
.lake/packages/."""
import re, os
root="/home/scaraven/Documents/Verified-zkEVM/leanerVM/.lake/packages"
A="Arklib/ArkLib/"; C="CompPoly/CompPoly/"; CL="Clean/Clean/"; V="VCVio/VCVio/"
checks=[
 (A+"OracleReduction/ProtocolSpec/Basic.lean", "", ["ProtocolSpec","Direction","MessageIdx","ChallengeIdx","FullTranscript","Transcript"]),
 (A+"OracleReduction/OracleInterface.lean","53-73",["OracleInterface"]),
 (A+"OracleReduction/OracleInterface.lean","93 (status E8)",["instDefault"]),
 (A+"OracleReduction/Basic.lean","222-669",["Prover","Verifier","OracleVerifier","Reduction","OracleReduction","OracleProof"]),
 (A+"OracleReduction/Basic.lean","1011 (status)",["PureForm"]),
 (A+"OracleReduction/Security/Basic.lean","89-103, 460-469",["completeness","perfectCompleteness"]),
 (A+"OracleReduction/Security/Basic.lean","248-359",["knowledgeSoundness","Straightline"]),
 (A+"OracleReduction/Security/Basic.lean","193 (status)",["perfectCompleteness_of_run_support"]),
 (A+"OracleReduction/Security/RoundByRound.lean","77-190, 416, 534, 606, 553",["KnowledgeStateFunction","RoundByRound","rbrKnowledgeSoundness","rbrKnowledgeSoundnessWorstCase","rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness","rbrKnowledgeSoundnessWorstCaseWith"]),
 (A+"OracleReduction/Security/Implications.lean","85",["rbrKnowledgeSoundness_implies_rbrSoundness","rbrKnowledgeSoundness_implies_knowledgeSoundness","rbrSoundness_implies_soundness"]),
 (A+"OracleReduction/Composition/Sequential/Append/Basic.lean","709",["append"]),
 (A+"OracleReduction/Composition/Sequential/General.lean","255",["seqCompose"]),
 (A+"OracleReduction/Composition/Sequential/Completeness.lean","",["seqCompose_perfectCompleteness_of_pure"]),
 (A+"OracleReduction/Composition/Sequential/Append/Completeness.lean","",["append_perfectCompleteness_of_pure_verifiers","append_perfectCompleteness_of_guarded_verifiers"]),
 (A+"OracleReduction/Composition/Sequential/GuardedNary.lean","",["seqCompose_completeness_of_guarded_verifiers"]),
 (A+"OracleReduction/Composition/Sequential/Append/RoundByRound.lean","37",["append_rbrSoundnessWorstCase_of_pure_first"]),
 (A+"OracleReduction/Composition/Sequential/Append/StateFunction.lean","292, 75",["append"]),
 (A+"OracleReduction/Composition/Sequential/Append/Security.lean","(status: 4 sorries)",["append_knowledgeSoundness","append_rbrKnowledgeSoundness"]),
 (A+"OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean","112 (status)",["GuardedForm"]),
 (A+"ProofSystem/Sumcheck/Spec/General.lean","171",["reduction"]),
 (A+"ProofSystem/Sumcheck/Spec/SingleRound.lean","130-144",["StatementRound","relationRound","verifier_rbrKnowledgeSoundness"]),
 (A+"ProofSystem/Sumcheck/Spec/Domain.lean","",["Domain"]),
 (A+"Data/MvPolynomial/Multilinear.lean","",["MLE","eqPolynomial","eqTilde","eqTilde_append","MLE_eq_zero_iff","MLEEquivFin"]),
 (A+"ToCompPoly/Multilinear/Basic.lean","56",["eval_eq_MvPolynomial_MLE"]),
 (A+"Data/MvPolynomial/SchwartzZippelCounting.lean","",["schwartz_zippel_counting","prob_eval_zero_le_div"]),
 (A+"OracleReduction/FiatShamir/Basic.lean","114-138",["fiatShamir","fsChallengeOracle","fiatShamir_completeness"]),
 (A+"Commitments/Functional/Basic.lean","",["Scheme","binding","perfectCorrectness_of_opening_perfectCompleteness","extractability"]),
 (A+"ProofSystem/ToyProblem/Codegen.lean","",[]),
 (A+"Data/Fin/Basic.lean","93 (status)",["induction_two"]),
 (A+"OracleReduction/Execution.lean","642, 663, 343 (status)",["run_of_verifier_first","run_of_prover_first","support_run_pure_verifier"]),
 (V+"OracleComp/Constructions/SampleableType.lean","44; 225 (status)",["SampleableType","probEvent_uniformSample"]),
 (V+"OracleComp/SimSemantics/OptionT/Basic.lean","49, 214 (status)",["simulateQ_optionT_bind_run","simulateQ_optionT_failure"]),
 (C+"Multilinear/Basic.lean","47; 410-632; status 475,499,520,543,600,632,482,512",["CMlPolynomialEval","evalMle","evalMleLayer","evalMle_succ","eval₂Mle","eval_mle_eq_eval","eqTilde","eqTilde_eq_prod","eqTilde_append","lagrangeBasis","evalMleLayer_get"]),
 (C+"Multilinear/Equiv.lean","",["toMvPolynomialDeg1","equivMvPolynomialDeg1"]),
 (C+"Multivariate/CMvPolynomial.lean","55-85; 231 (review)",["totalDegree"]),
 (C+"Fields/Binary/BF64/Ext3.lean","171, 199 (status)",["card_ext3"]),
 (C+"Fields/Binary/BF64/Impl.lean","391 (status)",["Fintype"]),
 (CL+"Circuit/Expression.lean","6-90; 71",["Expression","eval","fromArray"]),
 (CL+"Air/FlatComponent.lean","21; 151-186",["operations","Table","Constraints","environment"]),
 (CL+"Circuit/Operations.lean","404-432; 168-182",["constraints","interactions","constraintsHold_iff_forall_mem"]),
 (CL+"Circuit/Channel.lean","101-105, 305-329",["AbstractInteraction","Interaction"]),
 (CL+"Air/FlatEnsemble.lean","19-25; 361; 342; 353-360",["EnsembleWitness","Statement","BalancedChannels"]),
 (CL+"Circuit/WitnessGeneration.lean","82",["witgen"]),
]
KW=r"(?:def|theorem|lemma|structure|inductive|abbrev|instance|class|opaque)"
for f,cited,names in checks:
    p=os.path.join(root,f)
    if not os.path.exists(p):
        print(f"MISSING FILE  {f}   (cited {cited})"); continue
    ls=open(p).read().split("\n")
    print(f"{f}  [{len(ls)} lines]  cited: {cited}")
    for n in names:
        rx=re.compile(r"(?:^|\s)%s\s+(?:[^\s.]+\.)*%s(?=\s|$|\{|\(|\[|:)"%(KW,re.escape(n)))
        hits=[i for i,l in enumerate(ls,1) if rx.search(l)]
        sor=""
        print(f"    {n}: decl at {hits[:8] if hits else 'NOT FOUND as a declaration'}")
    ns=sum(1 for l in ls if re.search(r"\bsorry\b",l))
    if ns: print(f"    (lines containing 'sorry': {ns})")
