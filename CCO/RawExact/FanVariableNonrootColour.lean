import CCO.RawExact.FanVariableEdgeColours
import CCO.RawExact.FanPuncturedSupport
import Mathlib.Tactic

/-!
# B002 C12: all nonroot private-fan edges retain their original colours

Choose ANY genuine RAW word walk independently for each original
menu/list-slot occurrence, retaining the literal actual old centres.
Even if chosen roots and private interiors change, every specified
fan graph edge wholly away from the single formal root retains
EXACTLY the permanent reference old typed atomic colour.

This theorem combines the source's complete actual centre diagram
with the proved per-occurrence old word-colour invariance. There is
no SAP, global Helly witness or artificial equality atom.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- The single nonroot old-point assignment preserves all formal
graph-edge colours away from the root, for ANY independent family
of actual represented RAW walk witnesses. -/
theorem privateFanVariable_nonroot_adjacent_colour_eq_reference
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (v w : PrivateFanVertex S D centres)
    (hv : v ≠ privateFanRoot S D centres)
    (hw : w ≠ privateFanRoot S D centres)
    (hAdj : privateFanAdjacent S D centres v w) :
    taggedColour S
      (privateFanVariableReference S D centres choice xRoot v)
      (privateFanVariableReference S D centres choice xRoot w) =
    taggedColour S
      (privateFanNonrootReference S H D centres v)
      (privateFanNonrootReference S H D centres w) := by
  rcases hAdj with hOld | hPath
  · obtain ⟨c,d,hcd,heqV,heqW⟩ := hOld
    subst v
    subst w
    exact privateFanVariable_centre_colour_eq_reference
      S H D centres choice xRoot c d
  · obtain ⟨o,p,q,hpq,heqV,heqW⟩ := hPath
    subst v
    subst w
    have hp : p.val ≠ 0 := by
      intro hp0
      have hpStart : p = pathStart S (occurrenceWord S D o) :=
        Fin.ext hp0
      rw [hpStart, privateFanAt_start S D centres o] at hv
      exact hv rfl
    have hq : q.val ≠ 0 := by
      intro hq0
      have hqStart : q = pathStart S (occurrenceWord S D o) :=
        Fin.ext hq0
      rw [hqStart, privateFanAt_start S D centres o] at hw
      exact hw rfl
    exact privateFanVariable_nonroot_path_colour_eq_reference
      S H D centres choice xRoot o p q hp hq hpq

end CCO.RawExact
