# ArkLib landscape: what upstream implements, what is pending, what stays leanerVM's

Task `arklib-landscape` of the blueprint review. Written 2026-09-30. Sources and pins are named in
every section; the two ArkLib revisions are the OLD pin `dca90385` ("feat(module-system): migrate
to modules (#897)", 2026-09-09) and the NEW pin `7653a901` ("feat(sumcheck): compute honest
messages from CompPoly polynomials (#1243)", 2026-09-26). `origin/main` of `Verified-zkEVM/ArkLib`
was fetched on 2026-09-30 and its head IS the new pin (`git rev-list --count 7653a901..origin/main`
= 0; 347 commits separate the old pin from it). So "landed beyond the new pin" is empty today, and
everything not at the new pin lives in an open pull request or nowhere.

(Sections are appended as they are finished; a section that is missing was not reached.)

## 0. Summary

_(written last)_

