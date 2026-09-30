# A-notes (my own, section A), 2026-09-30

- CCHLRR ePrint 2018/1004 "Fiat-Shamir From Simpler Assumptions" (Canetti, Chen, Holmgren, Lombardi,
  G. Rothblum, R. Rothblum), submitted 2018-10-22. OPENED (pdftotext). Def 5.3 (RBR soundness, State
  function, 3 properties, eps per round); Prop 5.4 (RBR eps => standard soundness r*eps); Thm 5.8
  (RBR + R_State-correlation-intractable hash => adaptively sound FS argument; standard model, NOT ROM);
  §2.1: "Negligible round-by-round soundness readily implies state restoration soundness for a
  polynomial number of rewinds." No ROM error formula in the paper.
  STOC 2019 merged paper "Fiat-Shamir: From Practice to Theory" adds Wichs; pp. 1082-1090,
  doi 10.1145/3313276.3316380 (ACM PDF 403, not opened).
- Holmgren ePrint 2019/1261 "On Round-By-Round Soundness and State Restoration Attacks". OPENED.
  Thm 1.1 SR-sound => RBR sound (asymptotic); Thm 1.2 exists Pi with FS_RO[Pi] secure but not SR-sound.
- Block, Garreta, Katz, Thaler, Tiwari, Zajac, ePrint 2023/1071 (version 15 Feb 2024), Asiacrypt 2023.
  OPENED. Def 3.13 RBR knowledge (doomed set, extractor Ext(i,x,tau,m)); Thm 3.15 ([BCS16,CMS19,COS20]
  meta-theorem): eps_fs = Q*eps_rbr + 3(Q^2+1)/2^kappa; eps_fs-k = Q*eps_rbr-k + 3(Q^2+1)/2^kappa
  against Q-query adversaries (kappa = RO output bits); quantum: Theta(Q * eps_fs).
- Chiesa, Manohar, Spooner, ePrint 2019/834 (version 2020-01-14), TCC 2019. OPENED. Def 8.3 state
  function; Def 8.4 RBR soundness error; Def 8.5 RBR knowledge error k (poly-time extractor E(x,tr),
  if Pr_m[state(x,tr||m)=1] > k then (x,E(x,tr)) in R) -- "introduced in this work"; Thm 8.6 BCS in
  QROM: soundness O(t^2 eps + t^3/2^lambda); knowledge extraction prob Omega(mu - t^2 k - t^3/2^lambda).
- Chiesa, Yogev book, PDF compiled 2026-03-25 (475 pp.), snargsbook.org. OPENED. Def 31.1.1 state
  function; Def 31.1.2 RBR soundness errors (eps_i) per round, single eps = max; Claim 31.1.3 standard
  soundness <= sum_i eps_i <= k*eps; Def 31.1.6 RBR knowledge soundness errors, poly-time extractor from
  the IOP strings only (straightline); Claim 31.1.7; Thm 31.2.1 SR soundness eps_sr(s,n,t) <= (t+k) eps_rbr(n);
  Thm 31.3.1 kappa_sr <= (t+k) kappa_rbr; Thm 25.2.1 BCS soundness eps_ARG(lambda,n,t) <=
  eps_sr(lambda+s_FS,n,t) + kappa_MT^mm(lambda,(l_i),t,t+1) + t^2/2^lambda, and kappa^mm + t^2/2^lambda
  <= 3.5 t^2/2^lambda if t >= 2(log l + 1) l; Thm 26.1.1 knowledge analogue (rewinding SR knowledge,
  extraction time); §28.3.2 straightline: kappa_ARG <= kappa_sr + 3.5 t^2/2^lambda; worst-case kappa-bit
  security needs lambda = 3 kappa + 3, average-case lambda = 2 kappa + 3.
- leanVM spec Annex B line 84: "Interactive soundness error is then at most sum_i eps_i. After
  Fiat--Shamir, it is max_i eps_i per random-oracle query [CCHLRR19,BCS16]."
- leanVM whir_config.rs:26-27 "the Fiat--Shamir error per random-oracle query is the MAX of the entries,
  not their sum"; :36-38 SECURITY_BITS=128 RBR target; :57-60 QUERY_GRINDING_BITS=17 post-commit,
  pre-queries; :404-407 "This is an RBR target, not a claim that the sum of all interactive failure
  probabilities is bounded by 2^-target_security_bits."
- Merkle: crates/fiat_shamir/src/merkle.rs:7 `pub type Hash = [u8; 32];` BLAKE2s-256 leaves and pairs,
  no leaf/node domain separation, no salt.
- ArkLib pin RoundByRound.lean:154-163 KnowledgeStateFunction docstring cites "ABF26 Definition A.5";
  ArkLib blueprint references.bib:519-525 ABF26 = Arnon, Boneh, Fenzi, "Open Problems in List Decoding
  and Correlated Agreement", manuscript accompanying the EF Proximity Prize, 2026, proximityprize.org.
- Blueprint References (protocol-blueprint.md:1530-1531) misattribute CCHLRR19 authors ("A. Chiesa,
  Y. Cheng, M. Holmgren, ..."); leanVM refs.bib has them right (Canetti, Chen, Holmgren, Lombardi,
  G. Rothblum, R. Rothblum, Wichs). Blueprint :1533 "B. Nazarov, Ligerito (NA25)" wrong: Novakovic,
  Angeris (ePrint 2025/1187). Blueprint :1533-1534 gives BCHKS25 the title "Mutual correlated agreement
  up to the Johnson bound"; actual title "On Proximity Gaps for Reed--Solomon Codes" (ePrint 2025/2055).
- BCHKS25 ePrint 2025/2055 (PDF dated 2025-11-06, 49 pp.), OPENED: Thm 1.3 (UDR, loss), Cor 1.4
  (lossless UDR, a > gamma n + 1, delta >= 3 sqrt(2/n)), Thm 1.5 (Johnson: m = max(ceil(sqrt(rho)/(2 eta)),3),
  a > [2(m+1/2)^5 + 3(m+1/2) gamma rho]/(3 rho^{3/2}) n + (m+1/2)/sqrt(rho) => Delta([u0,u1],C^2) <= gamma),
  rho = k/n "not the rate but off-by-1/n". Section 4.3 "List correlated agreement" (Thm 4.6 to read).
