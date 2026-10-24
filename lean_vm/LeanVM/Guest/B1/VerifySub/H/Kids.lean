/-
  LeanVM.Guest.B1.VerifySub.H.Kids

  `verify_sub`'s thirteen callees on an honest child, each a `KidD` (the terminal on the results of
  `certify_placement` and `open_stacked`): their names, arguments, words read and results.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Own
public import LeanVM.Guest.B1.Terminal.KidsDep
public import LeanVM.Guest.B1.Terminal.TermComplete
public import LeanVM.Guest.B1.Placement.CertifyAt
public import LeanVM.Guest.B1.Place.OsCandAll
public import LeanVM.Guest.B1.Ring.TargetComplete
public import LeanVM.Guest.B1.Bits.Log2PlacedAll

/-!
# The callees

On the buffers' first words `bs` (`b i`, allocation order), the exponent tables at `lpE`, `sqE`:

0, 1. `g_power_of_word` on the rate's and the memory's log's words;
2. `log2_ceil_in_the_exponent__L0_L34` on `g^(push total)`;
3, 4. `assert_canonical` on the root's two words;
5. `verify_bus_gkr` on the stream past the announced words and the root, `zeta`;
6. `verify_tables` (B1-c's `VtHonest.args`, `linL` at `VsHonestB`);
7. `verify_keccak` on the stream past the tables' words, `chi`, the output lanes, `z_vals`, `slices`;
8. `ring_switch_target` on `slices` and the ring map's challenges;
9. `certify_placement` on `kappa_base` and `g_squares`;
10. `log2_ceil_in_the_exponent__L15_L34` on `g^(stack total)`;
11. `open_stacked`'s candidate on the stream past the Keccak reduction's words;
12. `check_opening_terminal`, on `certify_placement`'s buffers and `open_stacked`'s points when
    they are what those return (`vsTermOk`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- Buffer `i`'s first word. -/
def vb (bs : List ℕ) (i : ℕ) : ℕ := bs.getD i 0

/-- The GKR's cursor: past the announced words and the root. -/
def vcG (bs : List ℕ) : ℕ := vb bs 2 + 10

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- The stack's log. -/
def μs : ℕ := S.layout.stackLog

/-- The columns' logs. -/
def kappas : List ℕ := columnKappas S.logMem Tables.guestLogBytecode S.hs

/-- The opening's target. -/
noncomputable def target : E :=
  batchTarget (stackClaims S.layout S.claims S.km.1.1 S.km.1.2.1 S.km.1.2.2 (S.km.2 :: S.chs))
    S.lam

variable (bs : List ℕ)

/-- The tables' cursor. -/
def cT : ℕ := vcG bs + S.xsG.length

/-- The Keccak reduction's cursor. -/
def cK : ℕ := S.cT bs + S.xsT.length

/-- The opening's cursor. -/
def cW : ℕ := S.cK bs + S.xsK.length

/-- `verify_tables`' buffers. -/
def vtB (sqE : ℕ) : Tables.VtBases :=
  ⟨S.cT bs, vb bs 7, vb bs 4, vb bs 3, vb bs 6, sqE, vb bs 9, vb bs 0, vb bs 1, vb bs 10, 0⟩

/-- `certify_placement`'s result among the results before. -/
def cpRes (pv : List (List E × Main.Layout)) : List E × Main.Layout := pv.getD 9 ([], [])

/-- `open_stacked`'s result among the results before. -/
def osRes (pv : List (List E × Main.Layout)) : List E × Main.Layout := pv.getD 11 ([], [])

/-- The terminal is entered on what `certify_placement` and `open_stacked` return. -/
def termOk (pv : List (List E × Main.Layout)) : Prop :=
  Tables.cpOut S.logMem S.hs (cpRes pv).1 (cpRes pv).2 ∧ OsOut S.μs S.w (osRes pv).1 (osRes pv).2

/-- The terminal's own words: `zeta`, `chi`, `claim_cplen_g`, `lam_pool`, `z_vals`, `c_table`. -/
noncomputable def termLin : Main.Layout :=
  [(vb bs 7, S.point), (vb bs 10, S.chis), (vb bs 1, S.H.cplenW), (vb bs 15, lamW S.lam),
    (vb bs 11, zvW S.op S.kpt), (vb bs 14, ringCoefficients S.rchs)]

/-- **`verify_sub`'s callees on an honest child.** -/
noncomputable def kids (lpE sqE : ℕ) : List KidD :=
  [fun _ ↦ ⟨"g_power_of_word", true, [eOfNat S.rate], [], Returns [gen ^ S.rate]⟩,
    fun _ ↦ ⟨"g_power_of_word", true, [eOfNat S.logMem], [], Returns [gen ^ S.logMem]⟩,
    fun _ ↦ ⟨"log2_ceil_in_the_exponent__L0_L34", true,
      [gen ^ pushTotal S.logMem S.hs, ofK (gpow lpE), ofK (gpow sqE)], log2Lin lpE sqE,
      Returns [gen ^ max 0 (log2Ceil (pushTotal S.logMem S.hs))]⟩,
    fun _ ↦ ⟨"assert_canonical", true, [S.x0], [], Returns [0]⟩,
    fun _ ↦ ⟨"assert_canonical", true, [S.x1], [], Returns [0]⟩,
    fun _ ↦ ⟨"verify_bus_gkr", true,
      S.capS ++ [ofK (gpow (vcG bs)), gen ^ S.μ, ofK (gpow (vb bs 7))],
      [(vcG bs, S.xsG), (vb bs 7, S.point)],
      Returns (S.s5.cap ++ [ofK (gpow (vcG bs)) * gen ^ S.xsG.length] ++ S.vals)⟩,
    fun _ ↦ ⟨"verify_tables", true, S.H.args (S.vtB bs sqE), S.H.linL (S.vtB bs sqE),
      Returns (S.H.retsH (S.vtB bs sqE))⟩,
    fun _ ↦ ⟨"verify_keccak", true,
      S.s6.cap ++ [ofK (gpow (S.cK bs)), gen ^ S.τ, ofK (gpow (vb bs 10)),
        ofK (gpow (vb bs 0 + 110)), ofK (gpow (vb bs 11)), ofK (gpow (vb bs 12))],
      [(S.cK bs, S.xsK), (vb bs 10, S.chis), (vb bs 0 + 110, S.outs), (vb bs 11, S.op),
        (vb bs 11 + qkeccakVarsCap, S.kpt), (vb bs 12, S.slices)],
      Returns (S.s7.cap ++ [ofK (gpow (S.cK bs)) * gen ^ S.xsK.length, S.word, S.m0])⟩,
    fun _ ↦ ⟨"ring_switch_target", true, [ofK (gpow (vb bs 12)), ofK (gpow (vb bs 13))],
      [(vb bs 12, S.slices), (vb bs 13, S.rchs)],
      Returns [polyEval (S.slices.map (phiMap · S.rchs)) gen]⟩,
    fun _ ↦ ⟨"certify_placement", true, [ofK (gpow (vb bs 5)), ofK (gpow sqE)],
      Tables.cpLin S.logMem S.hs (vb bs 5) sqE, Tables.cpOut S.logMem S.hs⟩,
    fun _ ↦ ⟨"log2_ceil_in_the_exponent__L15_L34", true,
      [gen ^ Tables.stackTotal S.kappas, ofK (gpow lpE), ofK (gpow sqE)], log2Lin lpE sqE,
      Returns [gen ^ max 15 (log2Ceil (Tables.stackTotal S.kappas))]⟩,
    fun _ ↦ ⟨B1.Whir.openName S.μs S.rate, true,
      capOf S.s8.perm ++ [S.target, (digestScalars S.root).1, (digestScalars S.root).2,
        ofK (gpow (S.cW bs))],
      [(S.cW bs, S.xsW)], OsOut S.μs S.w⟩,
    fun pv ↦
      open Classical in
      ⟨"check_opening_terminal", decide (S.termOk pv),
        [ofK (gpow (vb bs 7)), ofK (gpow (vb bs 10)), S.H.rm, gen ^ S.μ, gen ^ S.H.n,
          gen ^ S.logMem, gen ^ S.τ, ofK (gpow (vb bs 1)), S.lam ^ 141, ofK (gpow (vb bs 15)),
          (cpRes pv).1.getD 1 0, (cpRes pv).1.getD 2 0, ofK (gpow (vb bs 11)),
          ofK (gpow (vb bs 14)), (osRes pv).1.getD 1 0, (osRes pv).1.getD 2 0,
          (osRes pv).1.getD 3 0, (osRes pv).1.getD 4 0, (osRes pv).1.getD 0 0],
        if S.termOk pv then (cpRes pv).2 ++ (osRes pv).2 ++ S.termLin bs else [],
        Returns []⟩]

theorem kids_length (lpE sqE : ℕ) : (S.kids bs lpE sqE).length = 13 := rfl

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
