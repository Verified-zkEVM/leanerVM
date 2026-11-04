/-
  LeanVM.Guest.B1.Sig.SphincsSig

  The leanSPHINCS signature `verify_sig_lean_sphincs` checks, read off its valuation and the frames
  of its three `sp_wots` calls.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsT
public import LeanVM.Guest.B1.Sig.SpWotsSound
public import LeanVM.Guest.B1.Main.Frames

/-!
# The signature `verify_sig_lean_sphincs` checks

`sphincsSigOf σ V` reads the signature off `verify_sig_lean_sphincs`'s valuation `σ` and the
frame map `V`; it mentions no hash.

* the randomizer `ρ`, `n3` (`sp_rand`);
* FORS tree `c`'s opening (`sForsOpeningOf`): its secret at the tree's base, and at each level the
  hinted child that is not the node climbed (`siblingOf`: the bit names the climbed one), the last
  the other top node, at the FORS key's cells;
* layer `l`'s signature (`sLayerOf`): its counter, the value of its four bytes; its chain values,
  `spValues` of the frame `V "sp_wots" [P, at, enc] [leaf]` of the layer's call; its path, the
  sibling of each level of `sp_path`.

The positions are the template's (`sBody`): the bottom layer's call `sWotsCall (at_b) enc_b leaf_b`
after the FORS key's encoding, an upper layer's in `sUpper` (`sUpperCtrOf`, `sUpperEncOf`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## Positions -/

/-- The counter of an upper layer from base `b`: its statements, next base and value. -/
def sUpperCtrOf (b : Nat) : List Stmt × Nat × V := sFromBytes (sMarks b 4).1 (sMarks b 4).2 g255W (b + 4)

/-- The encoding of an upper layer from base `b` over the root `below`. -/
def sUpperEncOf (below : V) (b : Nat) : List Stmt × Nat × Nat :=
  kMsg sPad [.cell sPP, .cell (.n ((sUpperCtrOf b).2.1 + 1)), .cell below, .cell (sUpperCtrOf b).2.2] 52
    false none ((sUpperCtrOf b).2.1 + 2)

/-- An upper layer, through its counter and encoding. -/
theorem sUpper_eq (adr below lane : V) (off height b : Nat) :
    sUpper adr below lane off height b =
      ([hintW "sp_counter" (runV b 4)] ++ (sUpperCtrOf b).1 ++
        [cst (sUpperCtrOf b).2.1 (word (tw 4) 0 0), addS (.n ((sUpperCtrOf b).2.1 + 1)) adr
          (.n (sUpperCtrOf b).2.1)] ++ (sUpperEncOf below b).1 ++
        [sWotsCall adr (.n (sUpperEncOf below b).2.2) (sUpperEncOf below b).2.1] ++
        (sPath lane off height 0 (.n (sUpperEncOf below b).2.1) ((sUpperEncOf below b).2.1 + 1)).1,
        (sPath lane off height 0 (.n (sUpperEncOf below b).2.1) ((sUpperEncOf below b).2.1 + 1)).2.1,
        (sPath lane off height 0 (.n (sUpperEncOf below b).2.1) ((sUpperEncOf below b).2.1 + 1)).2.2) :=
  rfl

/-- The base of the middle layer, and of the top one after its lane's constant. -/
def sBaseM : Nat := sPathB.2.1
def sBaseT : Nat := sUpperM.2.1 + 1

/-- Layer `l`'s key address cell `at`: `n(sH + 9)`, `n(sH + 10)`, `n(sH + 12)`. -/
def sAtOf (l : Nat) : V := if l = 0 then .n (sH + 9) else if l = 1 then .n (sH + 10) else .n (sH + 12)

/-- Layer `l`'s encoding digest's first cell. -/
def sEncOf (l : Nat) : V :=
  if l = 0 then .n sEncB.2.2 else if l = 1 then .n (sUpperEncOf sPathB.2.2 sBaseM).2.2
  else .n (sUpperEncOf sUpperM.2.2 sBaseT).2.2

/-- Layer `l`'s one-time leaf, `sp_wots`'s return. -/
def sLeafOf (l : Nat) : Nat :=
  if l = 0 then sEncB.2.1 else if l = 1 then (sUpperEncOf sPathB.2.2 sBaseM).2.1
  else (sUpperEncOf sUpperM.2.2 sBaseT).2.1

/-- Layer `l`'s counter's value. -/
def sCtrOf (l : Nat) : V :=
  if l = 0 then sCtrB.2.2 else if l = 1 then (sUpperCtrOf sBaseM).2.2 else (sUpperCtrOf sBaseT).2.2

/-- Layer `l`'s path's first bit: the field of its leaf. -/
def sOffOf (l : Nat) : Nat := if l = 0 then 0 else if l = 1 then 8 else 16

/-! ## Reading the values -/

/-- **The sibling of a node** whose two children are hinted at `x`, `x + 1`, the node climbed the
one the bit names: the left child when the bit is `1`. -/
def siblingOf (σ : Val) (bit : V) (x : Nat) : E :=
  if σ bit = 1 then σ (.n x) else σ (.n (x + 1))

/-- FORS tree `c`'s base: its secret's cell. -/
def sForsBase (c : Nat) : Nat := (sForsTrees c 0 1225).2.1

/-- **FORS tree `c`'s opening**: its secret, the siblings of its nine levels, the other top node. -/
def sForsOpeningOf (σ : Val) (c : Nat) : Sphincs.ForsTreeOpening where
  secret := cellVal (σ (.n (sForsBase c)))
  path l := cellVal (siblingOf σ (sBit (26 + 10 * c + l.val)) (sForsBase c + 22 + 23 * l.val))

/-- **Layer `l`'s one-time signature and path**, its chain values off the frame of its call. -/
noncomputable def sLayerOf (σ : Val) (V : FrameMap) (l : Sphincs.Layer) : Sphincs.LayerSignature l where
  counter := BitVec.ofNat 32 (cellNat (σ (sCtrOf l.val)))
  chainValues := spValues (V "sp_wots" [σ sPP, σ (sAtOf l.val), σ (sEncOf l.val)] [σ (.n (sLeafOf l.val))])
  authenticationPath j := cellVal (siblingOf σ (sBit (sOffOf l.val + j.val)) (sLeafOf l.val + 1 + 21 * j.val))

/-- **The leanSPHINCS signature `verify_sig_lean_sphincs` checks**, read off its valuation `σ` and
the frame map `V`. -/
noncomputable def sphincsSigOf (σ : Val) (V : FrameMap) : Sphincs.Signature where
  randomizer := cellVal (σ (.n 3))
  forsOpening c := sForsOpeningOf σ c.val
  layers l := sLayerOf σ V l

end
end LeanVM.Guest.B1.Sig
