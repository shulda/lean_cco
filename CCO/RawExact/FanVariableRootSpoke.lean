import CCO.RawExact.FanVariableTypedPoint
import CCO.RawExact.FanVariableEdgeColours
import CCO.RawExact.FanFullEdgeSemantics
import Mathlib.Tactic

/-!
# B002 C12: the chosen two RAW walks realize their original root spokes

The full finite private fan labels each root incident edge using a
genuinely old reference RAW-word atom. If a selected occurrence is
replaced by another actual old word walk whose starting point equals
the one chosen global root, the first edge's ORIGINAL atom remains
the same, even with identity letters and diagonal word outputs.

This lemma establishes the root-edge case of cycle-local
homomorphisms. All other occurrences may keep completely different
original old roots; global heterogeneous ball Helly is not assumed.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- The actual tagged pair-colour of the selected formal root
spoke agrees with the permanent reference atom whenever the
selected occurrence's original RAW walk starts at the chosen root. -/
theorem privateFanVariable_root_spoke_tagged_of_occurrence
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (v : PrivateFanVertex S D centres)
    (a : S.Atom root (privateFanSort S D centres v))
    (o : WordOccurrence S D)
    (q : PathPosition S (occurrenceWord S D o))
    (hq : q.val = 1)
    (hv : v = privateFanAtWordPosition S D centres o q)
    (hStart : (choice o).1 = xRoot)
    (hReference :
      taggedColour S
        (referencePointAt S H D centres o
          (pathStart S (occurrenceWord S D o)))
        (referencePointAt S H D centres o q) =
          (⟨root, privateFanSort S D centres v, some a⟩ :
            Σ i : ι, Σ j : ι, Option (S.Atom i j))) :
    taggedColour S
      (privateFanVariableReference S D centres choice xRoot
        (privateFanRoot S D centres))
      (privateFanVariableReference S D centres choice xRoot v) =
        (⟨root, privateFanSort S D centres v, some a⟩ :
          Σ i : ι, Σ j : ι, Option (S.Atom i j)) := by
  subst v
  exact
    (privateFanVariable_chosen_first_spoke_colour_eq_reference
      S H D centres choice xRoot o hStart q hq).trans hReference

/-- The selected true old atom on a root spoke is realized by
the dependent-typed point field required by the actual old source,
not just by its Sigma-valued pair-colour fingerprint. -/
theorem privateFanVariable_root_spoke_atom_of_occurrence
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (v : PrivateFanVertex S D centres)
    (a : S.Atom root (privateFanSort S D centres v))
    (o : WordOccurrence S D)
    (q : PathPosition S (occurrenceWord S D o))
    (hq : q.val = 1)
    (hv : v = privateFanAtWordPosition S D centres o q)
    (hStart : (choice o).1 = xRoot)
    (hReference :
      taggedColour S
        (referencePointAt S H D centres o
          (pathStart S (occurrenceWord S D o)))
        (referencePointAt S H D centres o q) =
          (⟨root, privateFanSort S D centres v, some a⟩ :
            Σ i : ι, Σ j : ι, Option (S.Atom i j))) :
    S.colour
      (privateFanVariableTypedPoint S D centres choice xRoot
        (privateFanRoot S D centres))
      (privateFanVariableTypedPoint S D centres choice xRoot v) =
      some a := by
  have hEncoded :=
    privateFanVariable_root_spoke_tagged_of_occurrence
      S H D centres choice xRoot v a o q hq hv hStart hReference
  rw [← privateFanVariableTypedPoint_tag S D centres choice xRoot
        (privateFanRoot S D centres),
      ← privateFanVariableTypedPoint_tag S D centres choice xRoot v]
    at hEncoded
  change (⟨root, privateFanSort S D centres v,
      S.colour
        (privateFanVariableTypedPoint S D centres choice xRoot
          (privateFanRoot S D centres))
        (privateFanVariableTypedPoint S D centres choice xRoot v)⟩ :
      Σ i : ι, Σ j : ι, Option (S.Atom i j)) =
    ⟨root, privateFanSort S D centres v, some a⟩ at hEncoded
  simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hEncoded

end CCO.RawExact
