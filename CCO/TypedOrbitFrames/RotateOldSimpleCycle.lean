import CCO.TypedOrbitFrames.ChordRotationFin
import CCO.TypedOrbitFrames.ChordShortLeft
import Lean.Elab.Tactic.Omega

/-!
# B053 C04: rotate an ACTUAL original typed SimpleCycle, not just a graph

For each cyclic origin s in ZMod n, the genuine finite-ordinal
translation is an injective reindexing commuting with the
original cyclic successor. Compose that embedding with the TRUE
typed source SimpleCycle.vertices to obtain another SimpleCycle
of the SAME original PartialDiagram, with literally the same
prescribed diversity atom on each rotated side.

The dependent old Atom(source sort,target sort), source D.edge,
and proof of non-identity are transported TOGETHER through the
accepted original old edge-existence congruence. We do not
assume a homomorphism of this cycle or a new CCO provider.
-/

namespace CCO.TypedOrbitFrames

universe u v w z
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}

/-- Reindex an ACTUAL old typed source SimpleCycle at the
arbitrary cyclic origin s, preserving the true original
displayed old atoms, vertex sort labels, and absence of
an artificial diagonal or nonedge completion. -/
def originalRotateOldSimpleCycle
    {D : PartialDiagram S V} (C : SimpleCycle D)
    (s : ZMod C.length) : SimpleCycle D := by
  letI : NeZero C.length := ⟨Nat.ne_of_gt C.length_pos⟩
  let r : Fin C.length ↪ Fin C.length := originalCycleRotateIndex s
  let e : Fin C.length ↪ V := r.trans C.vertices
  refine {
    length := C.length
    length_ge_three := C.length_ge_three
    length_pos := C.length_pos
    vertices := e
    next_ne := ?_
    specified := ?_
  }
  · intro p
    exact e.injective.ne
      (original_short_cycle_next_ne C.length_ge_three p)
  · intro p
    have hindex := original_cycle_rotate_next C.length_ge_three s p
    change ∃ a, D.edge
      (C.vertices (r p))
      (C.vertices (r (CCO.cyclicNext C.length_pos p))) _ =
        some a
    have hy : C.vertices
        (CCO.cyclicNext C.length_pos (r p)) =
        C.vertices (r (CCO.cyclicNext C.length_pos p)) :=
      congrArg C.vertices hindex.symm
    exact original_old_specified_edge_witness_congr S
      rfl hy
      (C.next_ne (r p))
      (e.injective.ne
        (original_short_cycle_next_ne C.length_ge_three p))
      (C.specified (r p))

end CCO.TypedOrbitFrames
