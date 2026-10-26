/-
  Statement.Fast.Schemes

  The signature schemes' verifiers as the compiled node checks and hint generator run them:
  `sequenceFin` with a constant-depth lookup, and the functions above it restated word for word,
  swapped in by `@[csimp]`.

  Speed only: `@[csimp]` lemmas, each proved, that change how the statement's definitions are
  compiled and nothing they mean. Not part of what a reviewer of `Statement/` must read.
-/

module

public import Statement.LeanXmss
public import Statement.LeanSphincs

/-!
# The compiled signature schemes

Both schemes collect a one-time key's chain ends with `sequenceFin`, which returns
`Fin.cases head tail`. Compiled, `Fin.cases` is `Fin.induction`, which evaluates the value below an
index before discarding it, so looking up index `i` looks up every index below it in the tail: a
lookup costs `2^i`, out of reach at the `58` and `64` chains of a leaf. `sequenceFin` is restated
here with `cons`, whose lookup peels one index, and proved equal (`sequenceFin_eq`); the
verifiers' functions that call it are restated word for word, each equal to its definition by
`rfl`, so that every module importing this one compiles them with it (a `@[csimp]` lemma acts
where code is compiled, so it does not reach the schemes' own modules; `Statement.LeanVmGuest`
imports this one, so the guest's specification and every module after it compile them so).
Nothing here transcribes a source.
-/

namespace LeanVM.Schemes.Fast

@[expose] public section

/-- `Fin.cases head tail`, looking up an index without the ones below it. -/
def cons {α : Type} {n : Nat} (head : α) (tail : Fin n → α) : Fin (n + 1) → α :=
  fun i ↦ if h : i.val = 0 then head else tail ⟨i.val - 1, by omega⟩

/-- `Fin.cases` is `cons`. -/
theorem cases_eq_cons {α : Type} {n : Nat} (head : α) (tail : Fin n → α) :
    (Fin.cases head tail : Fin (n + 1) → α) = cons head tail := by
  funext i
  induction i using Fin.cases with
  | zero => simp [cons]
  | succ j => simp [cons]

/-- `sequenceFin`, with `cons`. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} :
    {n : Nat} → (Fin n → m α) → m (Fin n → α)
  | 0, _ => pure Fin.elim0
  | n + 1, computation => do
    let head ← computation 0
    let tail ← sequenceFin fun index : Fin n ↦ computation index.succ
    return cons head tail

/-- The schemes' `sequenceFin` (leanSPHINCS's is leanXMSS's) is `sequenceFin`. -/
theorem sequenceFin_xmss {m : Type → Type} [Monad m] {α : Type} :
    ∀ {n : Nat} (computation : Fin n → m α),
      LeanXmss.Concrete.sequenceFin computation = sequenceFin computation
  | 0, _ => rfl
  | n + 1, computation => by
    simp only [LeanXmss.Concrete.sequenceFin, sequenceFin, cases_eq_cons]
    congr 1
    funext head
    rw [sequenceFin_xmss]

/-- The schemes' `sequenceFin` compiles as `sequenceFin`. -/
@[csimp] theorem xmss_sequenceFin_eq : @LeanXmss.Concrete.sequenceFin = @sequenceFin := by
  funext m _ α n computation
  exact sequenceFin_xmss computation

/-! ## leanXMSS -/

namespace Xmss

open LeanXmss LeanXmss.Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `LeanXmss.Concrete.otsLeaf`. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (randomness : Randomness) (values : ChainIndex → Digest) : m (Option Digest) := do
  let digest ← messageDigest parameter lay key message randomness
  let some encoding := Codeword.decode digest | return none
  let endpoints ← LeanXmss.Concrete.sequenceFin fun chainIdx =>
    recoverChain parameter lay key chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay key endpoints
  return some value

/-- `LeanXmss.Concrete.otsLeaf` compiles as its restatement. -/
@[csimp] theorem otsLeaf_eq : @LeanXmss.Concrete.otsLeaf = @otsLeaf := rfl

/-- `LeanXmss.Concrete.layerRoot`, with `otsLeaf`. -/
def layerRoot (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (message : HashInput)
    (part : LayerSignature) : m (Option Digest) := do
  let some leaf ← LeanXmss.Concrete.otsLeaf parameter lay key message part.randomness
    part.chainValues | return none
  let root ← treeFold parameter lay key part.path layerHeight leaf
  return some root

/-- `LeanXmss.Concrete.layerRoot` compiles as its restatement. -/
@[csimp] theorem layerRoot_eq : @LeanXmss.Concrete.layerRoot = @layerRoot := rfl

/-- `LeanXmss.Concrete.verify`, with `layerRoot`. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let index := signature.leafIndex
  let some bottomRoot ← LeanXmss.Concrete.layerRoot publicKey.parameter bottomLayer
      (keyAt index bottomLayer) (bytesLE 32 message) (signature.layers bottomLayer) | return false
  let some root ← LeanXmss.Concrete.layerRoot publicKey.parameter topLayer (keyAt index topLayer)
      (bytesLE 16 bottomRoot) (signature.layers topLayer) | return false
  return decide (root = publicKey.root)

/-- `LeanXmss.Concrete.verify` compiles as its restatement. -/
@[csimp] theorem verify_eq : @LeanXmss.Concrete.verify = @verify := by
  unfold LeanXmss.Concrete.verify
  rfl

end Xmss

/-! ## leanSPHINCS -/

namespace Sphincs

open _root_.Sphincs _root_.Sphincs.Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `Sphincs.Concrete.otsLeaf`. -/
def otsLeaf (parameter : PublicParameter) (leaf : Index) (message : ForestKey) (counter : Counter)
    (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode parameter leaf message counter | return none
  let endpoints ← LeanXmss.Concrete.sequenceFin fun chainIdx =>
    recoverChain parameter leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter leaf endpoints
  return some value

/-- `Sphincs.Concrete.otsLeaf` compiles as its restatement. -/
@[csimp] theorem otsLeaf_eq : @_root_.Sphincs.Concrete.otsLeaf = @otsLeaf := rfl

/-- `Sphincs.Concrete.verify`, with `otsLeaf`. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  let index := digestIndex digest
  let forestKey ← forestRecover publicKey.parameter index (digestMarks digest) signature.forest
  let some leaf ← _root_.Sphincs.Concrete.otsLeaf publicKey.parameter index forestKey
    signature.counter signature.chainValues | return false
  let root ← treeFold publicKey.parameter index
    (fun level ↦ if h : level < totalHeight then signature.path ⟨level, h⟩ else 0) totalHeight leaf
  return decide (root = publicKey.root)

/-- `Sphincs.Concrete.verify` compiles as its restatement. -/
@[csimp] theorem verify_eq : @_root_.Sphincs.Concrete.verify = @verify := by
  unfold _root_.Sphincs.Concrete.verify
  rfl

end Sphincs

end
end LeanVM.Schemes.Fast
