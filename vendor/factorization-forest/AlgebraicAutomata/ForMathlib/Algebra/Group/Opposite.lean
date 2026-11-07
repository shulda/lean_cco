/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/

/- CCO compatibility port, 6 November 2026.
Adapted from ReemMelamed/algebraic-automata at
0acb244aaa913c32eeeff48e939cb5df469a3f70 for the receiving
Lean 4.34.1 / Mathlib v4.34.1 environment. Original notices retained.
Compatibility modifications are recorded in PROVENANCE.json and PORT_REPORT.md. -/

module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Basic.Finite.Defs

/-!
# Finiteness of `MulOpposite`

This file provides the instance that `MulOpposite S` is finite
whenever `S` is finite.

Currently intended for a PR to mathlib4.
-/

@[expose] public section

variable {S : Type*}

instance [Finite S] : Finite Sᵐᵒᵖ := Finite.of_equiv S MulOpposite.opEquiv

end
