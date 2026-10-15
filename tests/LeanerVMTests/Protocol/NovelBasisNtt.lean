import LeanerVM.Protocol.NovelBasis
import CompPoly.Fields.Binary.AdditiveNTT.Executable
import Mathlib.Algebra.Algebra.ZMod

/-!
# The encoder against CompPoly's additive NTT

`encode` is `def:enc` read directly. CompPoly's `computableAdditiveNTT` is the fast algorithm of
`app:ntt` (Lin-Chung-Han, proved equal to the evaluation of the novel-basis polynomial in
`CompPoly.Fields.Binary.AdditiveNTT.Correctness`), instantiated here at `K` and the basis
`β c = e_c = g ^ c`, the blueprint's test "`encode` against CompPoly's additive NTT at `κ = 3`".
The two are compared in the kernel at position `5`, for the unit messages at `1` (`X_1 = Ŵ_0`) and
at `2` (`X_2 = Ŵ_1`, the first novel polynomial that is not a monomial). Kernel evaluation of
CompPoly's NTT is the limit: these take under two minutes, while a unit message at `6` or `7` and
a dense message did not finish in ten minutes, so the other messages and positions rest on the
Python vectors and on `vanish_eq` (`LeanerVMTests.Protocol.NovelBasis`).

The instantiation needs `β` independent over `F_2` (`basisElt_linearIndependent`, proved), and
`ℓ + R < r = 64`: the NTT is limited to `κ + R ≤ 63`, the bound of the Rust's
`AdditiveNttF64::standard` (`dim ≤ 63`), where Annex B allows `κ + R ≤ 64`.
-/

namespace LeanerVMTests.Protocol

open LeanerVM.Parameters LeanerVM.Protocol AdditiveNTT CompPoly

local instance : Algebra (ZMod 2) K := ZMod.algebra K 2
local instance : Fact (LinearIndependent (ZMod 2) (fun c : Fin 64 ↦ basisElt c)) :=
  ⟨basisElt_linearIndependent⟩
local instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨ZMod.card 2⟩
local instance : Fact (Nat.Prime (ringChar (ZMod 2))) :=
  ⟨by rw [ZMod.ringChar_zmod_n]; exact Nat.prime_two⟩
local instance : Fact ((fun c : Fin 64 ↦ basisElt c) 0 = 1) := ⟨by decide +kernel⟩
local instance : NeZero 64 := ⟨by norm_num⟩

/-- CompPoly's additive NTT on `2 ^ 3` novel-basis coefficients, rate `2 ^ -2`, at `β = e`. -/
def nttK (a : Fin (2 ^ 3) → K) : Fin (2 ^ (3 + 2)) → K :=
  computableAdditiveNTT (𝔽q := ZMod 2) (L := K) (r := 64) (ℓ := 3) (R_rate := 2)
    (h_ℓ_add_R_rate := by omega) (β := fun c : Fin 64 ↦ basisElt c) a

/-- The unit message at `j`. -/
def unitMsg (j : ℕ) : Fin (2 ^ 3) → K := fun i ↦ if i.val = j then 1 else 0

set_option maxRecDepth 100000 in
example : nttK (unitMsg 1) ⟨5, by decide⟩ =
    encode (RingHom.id K) 3 2 (Vector.ofFn (unitMsg 1)) ⟨5, by decide⟩ := by decide +kernel

set_option maxRecDepth 100000 in
example : nttK (unitMsg 2) ⟨5, by decide⟩ =
    encode (RingHom.id K) 3 2 (Vector.ofFn (unitMsg 2)) ⟨5, by decide⟩ := by decide +kernel

end LeanerVMTests.Protocol
