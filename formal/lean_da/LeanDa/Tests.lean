import LeanDa.Blake2s

/-! Known-answer tests of the BLAKE2s transcription: RFC 7693 Appendix B (`"abc"`), the empty
string, and the bytes `0, 1, 2, …` (mod 256) at lengths around block boundaries and at a cell's
2048 bytes, against Python's `hashlib.blake2s`. -/

open LeanDa

private def hex (d : Digest) : String :=
  String.join (d.toList.map fun b ↦ (String.ofList (Nat.toDigits 16 b.toNat)).leftpad 2 '0')

private def counting (n : ℕ) : List UInt8 := (List.range n).map Nat.toUInt8

#guard hex (blake2s "abc".toUTF8.toList) ==
  "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982"
#guard hex (blake2s []) ==
  "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9"
#guard hex (blake2s (counting 64)) ==
  "56f34e8b96557e90c1f24b52d0c89d51086acf1b00f634cf1dde9233b8eaaa3e"
#guard hex (blake2s (counting 65)) ==
  "1b53ee94aaf34e4b159d48de352c7f0661d0a40edff95a0b1639b4090e974472"
#guard hex (blake2s (counting 128)) ==
  "1fa877de67259d19863a2a34bcc6962a2b25fcbf5cbecd7ede8f1fa36688a796"
#guard hex (blake2s (counting 129)) ==
  "5bd169e67c82c2c2e98ef7008bdf261f2ddf30b1c00f9e7f275bb3e8a28dc9a2"
#guard hex (blake2s (counting 2048)) ==
  "2f468225d850273bf95418f2b22b773be32e32c0127ed548943e0defbe0632f6"
