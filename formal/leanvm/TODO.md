# TODO

## Completeness size cap

`LeanVM.completeness` assumes at most `2^19` steps, `2^23` words of memory and `2^23`
instructions. The deployed verifier admits more: its only limit is a commitment of
`2^28` cells (`MAX_MU = 28`). The cap of `2^19` is forced only by runs made entirely of
`BLAKE2S` steps, each of which costs about 275 cells. A run with few `BLAKE2S` steps
could have about six million steps. Replace the step bound with a condition that counts
`BLAKE2S` steps separately.

## `Spec/Node.lean` against Rust

The digests (statement, signer set, key and SPHINCS lists, DA list), the batching transcript and
`fixedCells` are transcribed and reviewed, not tested. Check them against vectors from
`rec_aggregation`.
