import CCO.RawExact.WordOccurrences
import CCO.RawExact.SortTrace
import CCO.RawExact.DistinctCentres

/-!
# B002 C12/C26: actual finite vertices of the private-word anchored fan

The graph has ONE formal target root, ONE marked vertex for every
DISTINCT actual tagged old centre, and private internal vertices
indexed by BOTH the word occurrence and the interior position in
that word. Identity letters contribute no vertex; identical words
still have disjoint private interiors. No logical equality is named
as a diversity edge.

This defines the vertex carrier and its actual original-sort
labelling; specifying its real atomic edges and proving the
simple-cycle classification are subsequent C12 obligations.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι}
variable {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- Private interior of a single reduced word occurrence. Both true
endpoints are excluded even if its text is repeated elsewhere. -/
abbrev PrivateInteriorPosition
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (o : WordOccurrence S D) :=
  { p : PathPosition S (occurrenceWord S D o) //
    p.val ≠ 0 ∧
    p.val ≠ diversityLength S (occurrenceWord S D o) }

/-- Real old centres are quotient by ACTUAL tagged equality; private
interiors are indexed by the full occurrence including list slot. -/
abbrev PrivateFanVertex
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :=
  Option (DistinctCentres sort centres) ⊕
    (Σ o : WordOccurrence S D, PrivateInteriorPosition S D o)

instance privateFanVertex_finite
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :
    Finite (PrivateFanVertex S D centres) := by
  unfold PrivateFanVertex PrivateInteriorPosition
  infer_instance

/-- Exactly one new formal root, regardless of original sort. -/
def privateFanRoot
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :
    PrivateFanVertex S D centres :=
  .inl none

/-- A centre is a literal point in the finite set of distinct old
tagged values, not one vertex per menu occurrence. -/
def privateFanCentre
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (c : DistinctCentres sort centres) :
    PrivateFanVertex S D centres :=
  .inl (some c)

/-- All interior vertices of different occurrences are distinct.
The source word itself need not have an injective old realization. -/
def privateFanInterior
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PrivateInteriorPosition S D o) :
    PrivateFanVertex S D centres :=
  .inr ⟨o, p⟩

/-- Every formal fan vertex has its genuine ORIGINAL named sort.
No quotient sorts, arbitrary atom tables or lifted automorphisms. -/
def privateFanSort
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :
    PrivateFanVertex S D centres → ι
  | .inl none => root
  | .inl (some c) => distinctCentreSort sort centres c
  | .inr ⟨o,p⟩ => pathSortAt S (occurrenceWord S D o) p.1

theorem privateFanCentre_injective
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :
    Function.Injective (privateFanCentre S D centres) := by
  intro c d h
  exact Option.some.inj (Sum.inl.inj h)

theorem privateFanRoot_ne_centre
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (c : DistinctCentres sort centres) :
    privateFanRoot S D centres ≠ privateFanCentre S D centres c := by
  simp [privateFanRoot, privateFanCentre]

theorem privateFanInterior_injective
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :
    Function.Injective
      (fun p : Σ o : WordOccurrence S D, PrivateInteriorPosition S D o =>
        privateFanInterior S D centres p.1 p.2) := by
  intro p q h
  exact Sum.inr.inj h

theorem privateFanRoot_ne_interior
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PrivateInteriorPosition S D o) :
    privateFanRoot S D centres ≠
      privateFanInterior S D centres o p := by
  simp [privateFanRoot, privateFanInterior]

theorem privateFanCentre_ne_interior
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (c : DistinctCentres sort centres)
    (o : WordOccurrence S D)
    (p : PrivateInteriorPosition S D o) :
    privateFanCentre S D centres c ≠
      privateFanInterior S D centres o p := by
  simp [privateFanCentre, privateFanInterior]

end CCO.RawExact
