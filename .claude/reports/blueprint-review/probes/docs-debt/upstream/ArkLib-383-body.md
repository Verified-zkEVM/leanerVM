[x] Completeness/Soundness unfolding tools & snippets - mainly tools for converting the monadic defs into the logical defs (Completeness.lean, ReductionLogic.lean, Simulation.lean, Lemmas.lean) + new cast definition of oracle reduction (OracleReduction/Cast.lean) with completeness/rbrks compatibility
[x] Completeness & rbrKnowledgeSoundness for all FRI-Binius protocols: Binary Basefold, Ring-switching, FRI-Binius, simple ring-switching construction (BBFSmallFieldIOPCS), completeness of BBFSmallFieldIOPCS
[x] Minor changes: reintroduce AdditiveNTT.lean with index changes, will be migrated to CompPoly later

Status: All PR-owned files are sorry-free; the top-level composed results inherit sorryAx from OracleReduction's composition layer

Built with the help of Codex, Claude, Cursor, Gemini.
---
- Archived PRs: https://github.com/Verified-zkEVM/ArkLib/pull/270 https://github.com/Verified-zkEVM/ArkLib/pull/296 https://github.com/Verified-zkEVM/ArkLib/pull/417