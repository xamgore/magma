#!/usr/bin/env python3
"""Assemble the 32 independently certified rows into a universal theorem.

The trajectories and master-key data live in Row00..Row31 Lean modules.
This generator only builds small proofs connecting their statements.
"""
import sys as _magma_sys
from pathlib import Path as _MagmaPath
_magma_sys.path.insert(0, str(_MagmaPath(__file__).resolve().parents[4]))
from pathlib import Path

root = Path(__file__).resolve().parents[4]

def save(path, lines):
    payload = "\n".join(lines + [""])
    if not path.exists() or path.read_text() != payload:
        path.write_text(payload)
    print("GENERATED", path.relative_to(root), path.stat().st_size, "bytes")

lines = [
    "module", "import all Init.Data.Range.Basic",
] + [
    f"public import Magma.Differential.NinePlus.PositiveRows.Row{i:02}"
    for i in range(32)
]
lines += [
    "set_option maxRecDepth 8192",
    "set_option maxHeartbeats 20000000",
    "@[expose] public section",
    "namespace Magma.DiffanNineRoundAllOneHotTrajectory",
    "open Magma",
    "open Magma.MultiRoundDDT",
    "open Magma.DiffanFiveRoundUniversalSupport",
    "open Magma.DiffanNineRoundPositiveRows",
    "",
    "/-- All 1,024 concrete nine-round trajectories are checked",
    "    by Lean, with independent RFC master-key witnesses for",
    "    each ordered pair of active bit positions. -/",
    "theorem all_oneHot_nine_round_trajectory (i j : Fin 32) :",
    "    ∃ master : V 256, ∃ base : FeistelState,",
    "      multiRoundDelta 9",
    "        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)",
    "        base (oneHotDifference i, 0#32)",
    "        = (0#32, oneHotDifference j) := by",
    "  fin_cases i",
]
lines += [f"  · exact row{i:02} j" for i in range(32)]
lines += ["", "end Magma.DiffanNineRoundAllOneHotTrajectory"]
save(root / "Magma/Differential/NinePlus/NineRoundAllOneHotTrajectory.lean", lines)

lines = [
    "module", "import all Init.Data.Range.Basic",
    "public import Magma.Differential.NinePlus.NineRoundAllOneHotTrajectory",
    "set_option maxRecDepth 8192",
    "set_option maxHeartbeats 20000000",
    "@[expose] public section",
    "namespace Magma.DiffanNineRoundAllOneHotPositive",
    "open Magma",
    "open Magma.MultiRoundDDT",
    "open Magma.DiffanFiveRoundUniversalSupport",
    "open Magma.DiffanNineRoundAllOneHotTrajectory",
    "",
    "private theorem positive_of_real_delta (n : Nat)",
    "    (keys : Fin n → V 32) (a b base : FeistelState)",
    "    (h : multiRoundDelta n keys base a = b) :",
    "    0 < xorDDT_rounds n keys a b := by",
    "  classical",
    "  unfold xorDDT_rounds",
    "  apply Finset.card_pos.mpr",
    "  refine ⟨base, ?_⟩",
    "  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h",
    "",
    "/-- For EVERY pair of one-hot outer differences there exists",
    "    a real RFC 8891 master key with positive nine-round DDT.",
    "    All 1,024 trajectory certificates were checked by the kernel. -/",
    "theorem all_oneHot_nine_round_positive (i j : Fin 32) :",
    "    ∃ master : V 256,",
    "      0 < xorDDT_rounds 9",
    "        (fun k : Fin 9 => roundKey master ⟨k.val, by omega⟩)",
    "        (oneHotDifference i, 0#32) (0#32, oneHotDifference j) := by",
    "  obtain ⟨master, base, hd⟩ :=",
    "    all_oneHot_nine_round_trajectory i j",
    "  exact ⟨master, positive_of_real_delta 9 _ _ _ _ hd⟩",
    "",
    "end Magma.DiffanNineRoundAllOneHotPositive",
]
save(root / "Magma/Differential/NinePlus/NineRoundAllOneHotPositive.lean", lines)
