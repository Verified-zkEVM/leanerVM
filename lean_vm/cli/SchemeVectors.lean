import Statement.LeanSphincs
import Statement.LeanXmss
import Statement.Fast.Schemes
import Statement.Fast.Keccak

/-!
# `scheme-vectors`: EthLib's test vectors on the statement's signature schemes, compiled

`lake exe scheme-vectors` runs the statement's leanSPHINCS and leanXMSS (`Statement/LeanSphincs.lean`,
`Statement/LeanXmss.lean`, over Keccak-f[1600] in `Id`) on EthLib's test vectors as leanVM vendors
them at the pin (`crates/signatures/tests/signatures/ethlib/{sphincs,xmss}` of `../.leanvm`, the
checkout `../leanvm-tree.sh` makes; the first argument overrides the directory):

* leanSPHINCS: key generation (`key_gen`: the public key of a seed), signing (`sign`: the
  signature of a seed and a message, byte for byte) and verification (`verify`);
* leanXMSS: key generation, verification and the signature's leaf index (`signature_index`); signing
  with `--xmss-sign` (each case builds two trees of `2^16` one-time keys).

A case whose output is `null` is an input the crate rejects for its length: the statement's
schemes take values of fixed sizes, so it is skipped. The exit code is `0` when every case passes.
Not a proof: evidence that the statement's schemes are the crate's.
-/

open HashSig

namespace SchemeVectors

/-- A hexadecimal digit's value. -/
def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- The bytes of a hexadecimal string, `0x` first. -/
def hexBytes (s : String) : List Nat :=
  let rec go : List Char → List Nat
    | a :: b :: rest => (16 * hexDigit a + hexDigit b) :: go rest
    | _ => []
  go ((s.drop 2).toString.toList)

/-- A little-endian number of `w` bits. -/
def le (w : Nat) (bytes : List Nat) : BitVec w :=
  BitVec.ofNat w (bytes.foldr (fun b acc => b + 256 * acc) 0)

/-- The 16 bytes at offset `o`. -/
def digestAt (bytes : List Nat) (o : Nat) : Digest := le 128 ((bytes.drop o).take 16)

/-- A field of a case's YAML: `key: value`, the quotes dropped. -/
def field (text : String) (key : String) : Option String :=
  (text.splitOn "\n").findSome? fun line =>
    let t := line.trimAscii.toString
    if t.startsWith (key ++ ": ") then
      some (((t.drop (key.length + 2)).toString.replace "'" "").replace "\"" "")
    else none

/-- A public key: the root, then the parameter. -/
def publicKeyOf (bytes : List Nat) : PublicKey := ⟨digestAt bytes 0, digestAt bytes 16⟩

/-- A leanSPHINCS signature (`sign/format.md`): the randomizer, 24 FORS openings of a secret and
10 path nodes, then the bottom, middle and top layers, each a 4-byte counter, 64 chain values and
its tree's siblings. -/
def sphincsSignatureOf (bytes : List Nat) : Sphincs.Signature :=
  let layerStart (layer : Sphincs.Layer) : Nat := 16 + 24 * 176 + 1156 * layer.val
  ⟨digestAt bytes 0,
    fun tree => ⟨digestAt bytes (16 + 176 * tree.val),
      fun level => digestAt bytes (16 + 176 * tree.val + 16 + 16 * level.val)⟩,
    fun layer => ⟨le 32 ((bytes.drop (layerStart layer)).take 4),
      fun chain => digestAt bytes (layerStart layer + 4 + 16 * chain.val),
      fun level => digestAt bytes (layerStart layer + 4 + 1024 + 16 * level.val)⟩⟩

/-- A leanXMSS signature (`sign/format.md`): the 4-byte leaf index, then the bottom and top
layers, each a randomizer, 58 chain values and 16 siblings. -/
def xmssSignatureOf (bytes : List Nat) : LeanXmss.Signature :=
  let layerStart (layer : LeanXmss.Layer) : Nat := 4 + 1200 * layer.val
  ⟨(le 32 (bytes.take 4)).toFin,
    fun layer => ⟨digestAt bytes (layerStart layer),
      fun chain => digestAt bytes (layerStart layer + 16 + 16 * chain.val),
      fun level => digestAt bytes (layerStart layer + 16 + 928 + 16 * level.val)⟩⟩

/-- A case's verdict. -/
inductive Verdict where
  | pass | fail | skip

/-- Runs one case of a kind on its YAML. -/
def runCase (kind : String) (text : String) : Verdict := Id.run do
  let some output := field text "output" | return .fail
  if output == "null" then return .skip
  let bytes (key : String) : List Nat := hexBytes ((field text key).getD "")
  match kind with
  | "sphincs/key_gen" =>
    let key := (Id.run (Sphincs.KeyGenerationAndSigning.keygenFromSeed (m := Id)
      LeanVM.Semantics.keccakF1600 (le 256 (bytes "seed")))).1
    return if key == publicKeyOf (hexBytes output) then .pass else .fail
  | "sphincs/sign" =>
    let (_, secretKey) := Id.run (Sphincs.KeyGenerationAndSigning.keygenFromSeed (m := Id)
      LeanVM.Semantics.keccakF1600 (le 256 (bytes "seed")))
    let signature := Id.run (Sphincs.KeyGenerationAndSigning.sign (m := Id)
      LeanVM.Semantics.keccakF1600 secretKey (le 256 (bytes "message")))
    return if signature == some (sphincsSignatureOf (hexBytes output)) then .pass else .fail
  | "sphincs/verify" =>
    let ok := Sphincs.verifyWithKeccak (publicKeyOf (bytes "public_key"))
      (le 256 (bytes "message")) (sphincsSignatureOf (bytes "signature"))
    return if ok == (output == "true") then .pass else .fail
  | "xmss/key_gen" =>
    let key := (Id.run (LeanXmss.KeyGenerationAndSigning.keygenFromSeed (m := Id)
      LeanVM.Semantics.keccakF1600 (le 256 (bytes "seed")))).1
    return if key == publicKeyOf (hexBytes output) then .pass else .fail
  | "xmss/sign" =>
    let (_, secretKey) := Id.run (LeanXmss.KeyGenerationAndSigning.keygenFromSeed (m := Id)
      LeanVM.Semantics.keccakF1600 (le 256 (bytes "seed")))
    let index := (field text "leaf_index").bind String.toNat? |>.getD 0
    let signature := Id.run (LeanXmss.KeyGenerationAndSigning.sign (m := Id)
      LeanVM.Semantics.keccakF1600 secretKey (BitVec.ofNat 32 index).toFin
      (le 256 (bytes "message")))
    return if signature == some (xmssSignatureOf (hexBytes output)) then .pass else .fail
  | "xmss/verify" =>
    let ok := LeanXmss.verifyWithKeccak (publicKeyOf (bytes "public_key"))
      (le 256 (bytes "message")) (xmssSignatureOf (bytes "signature"))
    return if ok == (output == "true") then .pass else .fail
  | "xmss/signature_index" =>
    let sig := bytes "signature"
    if sig.length != 2404 then return .skip
    return if (xmssSignatureOf sig).leafIndex.val == output.toNat?.getD 0 then .pass else .fail
  | _ => return .fail

end SchemeVectors

open SchemeVectors in
/-- The driver: every case of every kind, in order. -/
def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := (args.filter (!·.startsWith "--")).headD
    "../.leanvm/crates/signatures/tests/signatures/ethlib"
  let xmssSign := args.contains "--xmss-sign"
  let kinds := ["sphincs/key_gen", "sphincs/sign", "sphincs/verify", "xmss/key_gen", "xmss/verify",
    "xmss/signature_index"] ++ (if xmssSign then ["xmss/sign"] else [])
  let mut failed := 0
  let mut passed := 0
  let mut skipped := 0
  for kind in kinds do
    let dir := root / kind
    let entries ← dir.readDir
    let cases := (entries.map (·.fileName)).qsort (· < ·)
    for name in cases do
      let file := dir / name / "data.yaml"
      unless ← file.pathExists do continue
      let text ← IO.FS.readFile file
      let start ← IO.monoMsNow
      let verdict := runCase kind text
      let ms := (← IO.monoMsNow) - start
      match verdict with
      | .pass => passed := passed + 1; IO.println s!"{kind}/{name}: ok ({ms} ms)"
      | .skip => skipped := skipped + 1; IO.println s!"{kind}/{name}: skipped (an input of another length)"
      | .fail => failed := failed + 1; IO.println s!"{kind}/{name}: FAILED"
      (← IO.getStdout).flush
  IO.println s!"{passed} passed, {failed} failed, {skipped} skipped"
  return if failed == 0 && passed > 0 then 0 else 1
