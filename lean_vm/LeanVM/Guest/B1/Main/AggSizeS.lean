/-
  LeanVM.Guest.B1.Main.AggSizeS

  `AggSize.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Main.AggSize
public import LeanVM.Guest.B1.Main.AggLoop99CS
public import LeanVM.Guest.B1.Main.LoopAtS
public import LeanVM.Guest.B1.Tables.VtCSizeS

/-!
# `AggSize.lean` under any `BLAKE2S` semantics

Each definition and lemma of `AggSize.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (vtc_leaf_total)

@[expose] public section

variable {S : BlakeSem}

variable {fs : String → ℕ} {rd : Reader} {m : ℕ} {rest : List E} {t : Tree} {rets : List E}

set_option maxRecDepth 100000 in
theorem loop95S_total (hm : 0 < m) (hn : t.name = "__loop95")
    (hv : t.ValidB S coreProgram rd (1 :: gen ^ m :: rest) rets) (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * fs "__loop95" + fs "__loop95" :=
  leafLoopS_total find_loop95 core566_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 2125 rfl) (mem_of_getElem? 2126 rfl) (mem_of_getElem? 2127 rfl)
    (mem_of_getElem? 2128 rfl) (mem_of_getElem? 2129 rfl) hm hn hv hbo

set_option maxRecDepth 100000 in
theorem loop96S_total (hm : 0 < m) (hn : t.name = "__loop96")
    (hv : t.ValidB S coreProgram rd (1 :: gen ^ m :: rest) rets) (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * fs "__loop96" + fs "__loop96" :=
  leafLoopS_total find_loop96 core567_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 52 rfl) (mem_of_getElem? 53 rfl) (mem_of_getElem? 54 rfl)
    (mem_of_getElem? 55 rfl) (mem_of_getElem? 56 rfl) hm hn hv hbo

set_option maxRecDepth 100000 in
theorem loop97S_total (hm : 0 < m) (hn : t.name = "__loop97")
    (hv : t.ValidB S coreProgram rd (1 :: gen ^ m :: rest) rets) (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * fs "__loop97" + fs "__loop97" :=
  leafLoopS_total find_loop97 core569_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 257 rfl) (mem_of_getElem? 258 rfl) (mem_of_getElem? 259 rfl)
    (mem_of_getElem? 260 rfl) (mem_of_getElem? 261 rfl) hm hn hv hbo

set_option maxRecDepth 100000 in
theorem loop98S_total (hm : 0 < m) (hn : t.name = "__loop98")
    (hv : t.ValidB S coreProgram rd (1 :: gen ^ m :: rest) rets) (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * fs "__loop98" + fs "__loop98" :=
  leafLoopS_total find_loop98 core570_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 72 rfl) (mem_of_getElem? 73 rfl) (mem_of_getElem? 74 rfl)
    (mem_of_getElem? 75 rfl) (mem_of_getElem? 76 rfl) hm hn hv hbo

set_option maxRecDepth 100000 in
theorem loop99S_total (hm : 0 < m) (hn : t.name = "__loop99")
    (hv : t.ValidB S coreProgram rd (1 :: gen ^ m :: rest) rets) (hbo : t.BufsOk coreProgram) :
    t.total fs ≤ m * fs "__loop99" + fs "__loop99" :=
  leafLoopS_total find_loop99 core572_split rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (mem_of_getElem? 1187 rfl) (mem_of_getElem? 1188 rfl) (mem_of_getElem? 1189 rfl)
    (mem_of_getElem? 1190 rfl) (mem_of_getElem? 1191 rfl) hm hn hv hbo

set_option maxRecDepth 100000 in
theorem bs22S_total {args : List E} (hn : t.name = "batch_sumcheck__L22")
    (hv : t.ValidB S coreProgram rd args rets) (hbo : t.BufsOk coreProgram) :
    t.total fs = fs "batch_sumcheck__L22" :=
  vtcS_leaf_total find_bs22 core568_split (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hn hv hbo

set_option maxRecDepth 100000 in
theorem bs28S_total {args : List E} (hn : t.name = "batch_sumcheck__L28")
    (hv : t.ValidB S coreProgram rd args rets) (hbo : t.BufsOk coreProgram) :
    t.total fs = fs "batch_sumcheck__L28" :=
  vtcS_leaf_total find_bs28 core571_split (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hn hv hbo

end
end LeanVM.Guest.B1.Main
