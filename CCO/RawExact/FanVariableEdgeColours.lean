import CCO.RawExact.FanVariableReference
import CCO.RawExact.WalkReferenceColourTransport
import CCO.RawExact.FanNonrootRealization
import Mathlib.Tactic

/-!
# B002 C12: reference colours survive replacing just two RAW private walks

A chosen family of actual RAW word walks fixes the same literal old
centres as the permanent fan. At any NONROOT edge of one private
word occurrence, it has the same old typed pair-colour as the
permanent reference walk (all original identity letters are erased
as edge-free steps).

If an occurrence is rooted at the chosen global old root, its
FIRST formal spoke also keeps precisely the permanent source atom.
These lemmas require NO simultaneous root for other occurrences,
and NO Helly, CCO or SAP hypothesis.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- Every private-path edge avoiding the root retains exactly
its original reference atom under ANY replacement walks, no
matter which actual old roots these walks use. -/
theorem privateFanVariable_nonroot_path_colour_eq_reference
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (o : WordOccurrence S D)
    (p q : PathPosition S (occurrenceWord S D o))
    (hp : p.val ≠ 0) (hq : q.val ≠ 0)
    (hpq : pathAdjacent S (occurrenceWord S D o) p q) :
    taggedColour S
      (privateFanVariableReference S D centres choice xRoot
        (privateFanAtWordPosition S D centres o p))
      (privateFanVariableReference S D centres choice xRoot
        (privateFanAtWordPosition S D centres o q)) =
    taggedColour S
      (privateFanNonrootReference S H D centres
        (privateFanAtWordPosition S D centres o p))
      (privateFanNonrootReference S H D centres
        (privateFanAtWordPosition S D centres o q)) := by
  rw [privateFanVariableReference_at_nonroot S D centres choice xRoot o p hp,
    privateFanVariableReference_at_nonroot S D centres choice xRoot o q hq,
    privateFanNonrootReference_at_nonroot S H D centres o p hp,
    privateFanNonrootReference_at_nonroot S H D centres o q hq]
  exact occurrence_walk_reference_edge_colours
    S H D centres o (choice o).2 p q hpq

/-- The complete marked-centre diagram is literally unchanged
by ANY choice of private RAW walk witnesses. Distinct actual
tagged centres are neither collapsed nor renamed. -/
theorem privateFanVariable_centre_colour_eq_reference
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (c d : DistinctCentres sort centres) :
    taggedColour S
      (privateFanVariableReference S D centres choice xRoot
        (privateFanCentre S D centres c))
      (privateFanVariableReference S D centres choice xRoot
        (privateFanCentre S D centres d)) =
    taggedColour S
      (privateFanNonrootReference S H D centres
        (privateFanCentre S D centres c))
      (privateFanNonrootReference S H D centres
        (privateFanCentre S D centres d)) := rfl

/-- A private RAW word whose chosen actual start is the GLOBAL
root preserves the exact original colour of its first formal
spoke, even when all other word witnesses have different roots. -/
theorem privateFanVariable_chosen_first_spoke_colour_eq_reference
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (o : WordOccurrence S D)
    (hRoot : (choice o).1 = xRoot)
    (q : PathPosition S (occurrenceWord S D o))
    (hq : q.val = 1) :
    taggedColour S
      (privateFanVariableReference S D centres choice xRoot
        (privateFanRoot S D centres))
      (privateFanVariableReference S D centres choice xRoot
        (privateFanAtWordPosition S D centres o q)) =
    taggedColour S
      (referencePointAt S H D centres o
        (pathStart S (occurrenceWord S D o)))
      (referencePointAt S H D centres o q) := by
  have hqNonzero : q.val ≠ 0 := by omega
  have hFirst := privateFanVariableReference_at_start
    S D centres choice xRoot o hRoot
  have hNext := privateFanVariableReference_at_nonroot
    S D centres choice xRoot o q hqNonzero
  have hpq : pathAdjacent S (occurrenceWord S D o)
      (pathStart S (occurrenceWord S D o)) q :=
    (pathAdjacent_start_iff S (occurrenceWord S D o) q).mpr hq
  have hColour := occurrence_walk_reference_edge_colours
    S H D centres o (choice o).2
      (pathStart S (occurrenceWord S D o)) q hpq
  rw [privateFanAt_start S D centres o] at hFirst
  rw [hFirst, hNext]
  exact hColour

end CCO.RawExact
