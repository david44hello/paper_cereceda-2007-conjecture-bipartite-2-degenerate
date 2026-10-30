/-
Cereceda/Defs/Example2.lean — the instance on two vertices of the example after Lemma 3.4 (short v4.24 l. 474-477):
the sink `s` and one more vertex `u` with `N⁺(u) = {s}`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE (v4.24 l. 474-475). Vertices `s, u` = `Fin 2` (`s` = `0`, `u` = `1`), instance order = index, sink `s` with
the list `{0,1}`, `g = 0` and `x = 1`; `N⁺(u) = {s}` and `L(u) = {0,1,2,3}`.
-/
import Cereceda.Defs.Instance

namespace Cereceda

open Finset

/-- Out-neighbours of the example instance: `N⁺(u) = {s}`, the sink has none. -/
def ex2Out : Fin 2 → Finset (Fin 2)
  | 1 => {0}
  | _ => ∅

/-- Lists of the example instance: `L(s) = {0, 1}`, `L(u) = {0, 1, 2, 3}`. -/
def ex2L : Fin 2 → Finset (Fin 4)
  | 0 => {0, 1}
  | _ => {0, 1, 2, 3}

/-- The example after Lemma 3.4 (v4.24 l. 474-475): "let the sink `s` have the list `{0,1}` and `x = 1`, and let one
more vertex `u`, with `N⁺(u) = {s}`, have the list `{0,1,2,3}`" (`s` = `0`, `u` = `1`, `g = 0`, instance order =
index). -/
def ex2 : Instance (Fin 2) where
  sink := 0
  rank v := v.val
  rank_inj := fun a b h => Fin.ext h
  sink_first := fun v => Nat.zero_le _
  out := ex2Out
  out_before := by decide
  out_card := by decide
  sink_out := rfl
  L := ex2L
  L_card := by decide
  g := 0
  x := 1
  g_lt_x := by decide
  L_sink := rfl

end Cereceda
