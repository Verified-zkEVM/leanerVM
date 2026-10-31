import Sphincs.H0PTab
import Sphincs.H0NTab
import SphincsFors.H0Round

/-! **The checks of the lifetime certificates.** The Poisson tables (`PoisT`, `checkPT`), the
options of the small and large routes (`OptF`, `checkOptF`), the near certificates (`OptN`,
`checkOptN`), the covers of the large budgets (`CoverW`, `checkCoverW`, `checkCoverH`,
`ForsPotential.checkCoversH`) and the small route's check (`ForsPotential.checkSmallF`): the
functions `LifetimeCertificates.lean` evaluates with `decide +kernel`. Each is proved sound where
the bound it certifies is (`H0ForestCert.lean`, `H0ForestOpt.lean`, `H0NearOpt.lean`,
`BridgeDetW.lean`, `BridgeHeavyCert.lean`, `BridgeDetCloseF.lean`); here they read the moment
tables and the rounding alone, so that the certificates do not depend on the scheme, the statement
or the proofs. -/

namespace SphincsLayered.Security.ForsPotential

/-- Rational form of the weighted baseline at budget `qb`: `(2 (2^128 - qb) + 1) / 2^256`. -/
def betaWQ (qb : ℕ) : ℚ := (2 * ((2 : ℚ) ^ 128 - qb) + 1) / 2 ^ 256

end SphincsLayered.Security.ForsPotential

namespace SphincsLayered.Security.H0

open SphincsFors.Security.H0

/-! ### Poisson tables -/

/-- A Poisson table: rate bound `m / 2^64`, weight bounds `pm[n] / 2^P` for `n ≤ n1 + 1`, and `J`
series terms for `e^μ̄`. -/
structure PoisT where
  m : ℕ
  P : ℕ
  J : ℕ
  pm : List ℕ

namespace PoisT

def mu (t : PoisT) : ℚ := (t.m : ℚ) / 2 ^ 64
def n1 (t : PoisT) : ℕ := t.pm.length - 2
def pb (t : PoisT) (n : ℕ) : ℚ := (t.pm.getD n 0 : ℚ) / 2 ^ t.P
def r (t : PoisT) : ℚ := t.mu / (t.n1 + 2)

end PoisT

/-- The check of a Poisson table. -/
def checkPT (t : PoisT) : Bool :=
  decide (2 ≤ t.pm.length) &&
    decide ((2 : ℚ) ^ t.P ≤ (t.pm.getD 0 0 : ℚ) * expLow t.mu t.J t.P) &&
    decide (∀ n < t.pm.length - 1, t.pm.getD n 0 * t.m ≤ t.pm.getD (n + 1) 0 * ((n + 1) * 2 ^ 64)) &&
    decide (t.r < 1)

/-- Nonnegative, increasing and convex, with an extension slope at least the last increment. -/
def checkLeaf (tab : List ℚ) (J : ℚ) : Bool :=
  decide (2 ≤ tab.length) && decide (0 ≤ tab.getD 0 0) &&
    decide (∀ n < tab.length - 1, tab.getD n 0 ≤ tab.getD (n + 1) 0) &&
    decide (∀ n < tab.length - 2, 2 * tab.getD (n + 1) 0 ≤ tab.getD n 0 + tab.getD (n + 2) 0) &&
    decide (tab.getD (tab.length - 1) 0 - tab.getD (tab.length - 2) 0 ≤ J)

/-! ### Options -/

/-- The per-index weight `2^-26` of the cover probability. -/
def κQ : ℚ := 1 / 2 ^ 26

/-- One option of the certificate. -/
structure OptF where
  c1 : ℚ
  θ : ℚ
  cthr : ℚ
  s : ℕ
  eC : ℚ
  A2 : ℚ
  gt : List ℚ
  Jg : ℚ
  ht : List ℚ
  Jh : ℚ
  Eg : ℚ
  Ee : ℚ
  B : ℚ

/-- The excess part bound at `n` from the moment tables. -/
def gBound (o : OptF) (n : ℕ) : ℚ :=
  min (κQ * P1tab.getD n 0 ^ 8) (κQ ^ 2 * P2tab.getD n 0 ^ 8 / (4 * o.c1))

/-- The Chernoff factor bound (minus one) at `n` from the moment tables. -/
def hBound (o : OptF) (n : ℕ) : ℚ :=
  min (o.eC - 1) (o.θ * κQ * P1tab.getD n 0 ^ 8 + o.A2 * κQ ^ 2 * P2tab.getD n 0 ^ 8)

/-- The check of an option against a Poisson table, for subtree height `b`. -/
def checkOptF (b : ℕ) (t : PoisT) (o : OptF) : Bool :=
  decide (0 < o.c1) && decide (0 < o.θ) && decide (0 ≤ o.cthr) && decide (o.θ * o.c1 < 2 ^ o.s) &&
    decide (expUp (o.θ * o.c1) o.s t.P ≤ o.eC) &&
    decide ((o.eC - 1 - o.θ * o.c1) / o.c1 ^ 2 ≤ o.A2) &&
    decide (t.n1 ≤ 150) && decide (o.gt.length = t.n1 + 1) && decide (o.ht.length = t.n1 + 1) &&
    checkLeaf o.gt o.Jg && checkLeaf o.ht o.Jh &&
    decide (∀ n < t.n1 + 1, gBound o n ≤ o.gt.getD n 0) &&
    decide (∀ n < t.n1 + 1, hBound o n ≤ o.ht.getD n 0) &&
    decide (κQ ≤ o.gt.getD t.n1 0 + o.Jg) && decide (o.eC - 1 ≤ o.ht.getD t.n1 0 + o.Jh) &&
    decide ((((List.range (t.n1 + 1)).map fun n => t.pb n * o.gt.getD n 0).sum +
      t.pb (t.n1 + 1) * (o.gt.getD t.n1 0 / (1 - t.r) + o.Jg / (1 - t.r) ^ 2)) ≤ o.Eg) &&
    decide ((((List.range (t.n1 + 1)).map fun n => t.pb n * o.ht.getD n 0).sum +
      t.pb (t.n1 + 1) * (o.ht.getD t.n1 0 / (1 - t.r) + o.Jh / (1 - t.r) ^ 2)) ≤ o.Ee) &&
    decide (2 ^ b * o.Eg + sqUp t.P b (1 + o.Ee) / (expLow (o.θ * o.cthr) t.J t.P * eLowQ * o.θ) ≤ o.B) &&
    decide (0 ≤ o.Eg) && decide (0 ≤ o.Ee)

/-! ### Near certificates -/

/-- The near bound at `n` from the moment tables. -/
def nBound (n : ℕ) : ℚ := 16 * κQ * PHtab.getD n 0 * P1tab.getD n 0 ^ 7

/-- A near certificate: the table, its extension slope, and its Poisson mean. -/
structure OptN where
  nt : List ℚ
  Jn : ℚ
  En : ℚ

/-- The check of a near certificate against a Poisson table. -/
def checkOptN (t : PoisT) (o : OptN) : Bool :=
  decide (t.n1 ≤ 150) && decide (o.nt.length = t.n1 + 1) && checkLeaf o.nt o.Jn &&
    decide (∀ n < t.n1 + 1, nBound n ≤ o.nt.getD n 0) && decide (16 * κQ ≤ o.nt.getD t.n1 0 + o.Jn) &&
    decide ((((List.range (t.n1 + 1)).map fun n => t.pb n * o.nt.getD n 0).sum +
      t.pb (t.n1 + 1) * (o.nt.getD t.n1 0 / (1 - t.r) + o.Jn / (1 - t.r) ^ 2)) ≤ o.En)

/-! ### Covers of the large budgets -/

/-- Keygen credit `K` of the forest signer: the `226 · 2^b + 2 (26 − b)` hash calls of key
generation from the scheme seed (`Prefix.hashCalls_keygenFromMaster`), with one seed derivation for
the starts of two chains. The call deriving the scheme seed is not credited. -/
def kCreditF (b : ℕ) : ℕ := 226 * 2 ^ b + 2 * (26 - b)

/-- A cover entry: budgets `[qa, qb]` and the index of its option. -/
abbrev EntryF := ℕ × ℕ × ℕ

/-- A forest cover: a Poisson table, options, entries. -/
structure CoverW where
  qtop : ℕ
  tab : PoisT
  opts : List OptF
  entries : List EntryF

/-- The inverse landing probability at subtree height `b`. -/
def scanMb (b : ℕ) : ℕ := 2 ^ (26 - b)

/-- The cap on the landed pairs at subtree height `b` and budget `q`. -/
def lmaxB (b q : ℕ) : ℕ := 65 * ((q + 64 * scanMb b - 1) / (64 * scanMb b)) + 2 ^ 15

/-- The identity mass of a group, times `2^128`, at subtree height `b` and budget `q`. -/
def denB (b q : ℕ) : ℕ := 2 ^ 128 - (q + 2 ^ 32 + (scanMb b - 1) * lmaxB b q)

/-- The scan coin is fair up to the budget `qtop`, and the table rate covers the signatures and the
creations of the scan signer (`(2 − landing) q / denB` per unit) at every budget `q ≤ qtop`. -/
def checkRate (b N qtop : ℕ) (t : PoisT) : Bool :=
  decide (qtop + 2 ^ 32 + (scanMb b - 1) * lmaxB b qtop + (2 * scanMb b - 1) ≤ 2 ^ 128) &&
    decide ((N : ℚ) / 2 ^ b + ((2 * scanMb b - 1 : ℕ) : ℚ) * qtop / (scanMb b * denB b qtop * 2 ^ b) ≤ t.mu)

/-- The check of one entry. -/
def checkEntryF (b N : ℕ) (opts : List OptF) (e : EntryF) : Bool :=
  match opts[e.2.2]? with
  | none => false
  | some o =>
      decide (2 * e.2.1 ≤ 2 ^ 128) && decide (o.cthr ≤ ForsPotential.betaWQ e.2.1) &&
        decide ((e.2.1 : ℚ) * o.B + ((e.2.1 : ℚ) + kCreditF b + N) / 2 ^ 200 ≤
          ((e.1 : ℚ) / 2 ^ 128) ^ 2 + (kCreditF b : ℚ) / 2 ^ 127)

/-- Consecutive entries cover `[last, 2^127]`. -/
def chainF (b N qtop : ℕ) (opts : List OptF) : ℕ → List EntryF → Bool
  | last, [] => decide (qtop < last)
  | last, e :: rest => decide (e.1 ≤ last) && checkEntryF b N opts e && chainF b N qtop opts (e.2.1 + 1) rest

/-- A cover of every budget `qstart ≤ q ≤ qtop`. -/
def checkCoverW (b N qstart : ℕ) (c : CoverW) : Bool :=
  checkRate b N c.qtop c.tab && checkPT c.tab && c.opts.all (checkOptF b c.tab) &&
    chainF b N c.qtop c.opts qstart c.entries

/-- The identity mass of a group under the heavy coin, times `2^128`, at subtree height `b` and
budget `q`. -/
def denHB (b q : ℕ) : ℕ := 2 ^ 128 - (q / 2 + (scanMb b - 1) * lmaxB b q)

/-- The heavy coin is fair up to the budget `qtop`, and the table rate covers `N + 1` signatures and
the creations of the scan signer under the heavy coin at every budget `q ≤ qtop`. -/
def checkRateH (b N qtop : ℕ) (t : PoisT) : Bool :=
  decide (qtop / 2 + (scanMb b - 1) * lmaxB b qtop + (2 * scanMb b - 1) ≤ 2 ^ 128) &&
    decide (((N : ℚ) + 1) / 2 ^ b +
      ((2 * scanMb b - 1 : ℕ) : ℚ) * qtop / (scanMb b * denHB b qtop * 2 ^ b) ≤ t.mu)

/-- A heavy cover of every budget `qstart ≤ q ≤ qtop`. -/
def checkCoverH (b N qstart : ℕ) (c : CoverW) : Bool :=
  checkRateH b N c.qtop c.tab && checkPT c.tab && c.opts.all (checkOptF b c.tab) &&
    chainF b N c.qtop c.opts qstart c.entries

end SphincsLayered.Security.H0

namespace SphincsLayered.Security.ForsPotential

/-- The rational small-route check at the right end `qh` of the small budgets: the coin term is
`(2 M − 1) qh / (M 2^129)` with `M = 2^(26 − b)` (the creation rate of the scan signer), the near term
is multiplied by `κ = 2 - ρ + qh / 2^128 + N · 123 / (2^b 2^15)`. -/
def checkSmallF (b N qh : ℕ) (ρ cthr B c : ℚ) : Bool :=
  decide (3 / 2 ≤ ρ) && decide (ρ ≤ 2) &&
    decide (1 + 4032 * (2 - ρ) * ((qh : ℚ) / 2 ^ 128) ≤ ρ) && decide (1 + 66 * ((qh : ℚ) / 2 ^ 128) ≤ ρ) &&
    decide (64 * ((qh : ℚ) / 2 ^ 128) ≤ 1) && decide (qh ≤ 2 ^ 127) && decide (N ≤ 2 ^ 70) &&
    decide (cthr ≤ ρ / 2 ^ 128) && decide (0 ≤ B) && decide (0 ≤ c) &&
    decide ((N : ℚ) * 123 / (2 ^ b * 2 ^ 15) ≤ ρ - 1 - (qh : ℚ) / 2 ^ 128) &&
    decide (ρ + 2 ^ 128 * B + (2 * (H0.scanMb b : ℚ) - 1) * (qh : ℚ) / ((H0.scanMb b : ℚ) * 2 ^ 129) +
      (2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) * 123 / (2 ^ b * 2 ^ 15)) * qh * c + 1 / 2 ^ 60 ≤ 2)

/-- A chain of heavy covers of the large budgets, ending once every budget `q'` with
`q' + keygenCost < 2^127` is covered. -/
def checkCoversHeavy (b N : ℕ) : ℕ → List H0.CoverW → Bool
  | qstart, [] => decide (2 ^ 127 ≤ qstart + (226 * 2 ^ b + 2 * (26 - b)))
  | qstart, c :: heavy => H0.checkCoverH b N qstart c && checkCoversHeavy b N (c.qtop + 1) heavy

/-- A chain of covers of the large budgets: light covers first, then heavy covers. -/
def checkCoversH (b N : ℕ) : ℕ → List H0.CoverW → List H0.CoverW → Bool
  | qstart, [], heavy => checkCoversHeavy b N qstart heavy
  | qstart, c :: light, heavy => H0.checkCoverW b N qstart c && checkCoversH b N (c.qtop + 1) light heavy

end SphincsLayered.Security.ForsPotential
