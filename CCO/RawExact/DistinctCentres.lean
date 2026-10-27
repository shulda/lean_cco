import CCO.RawExact.AtomicFans

/-!
# B002 C12: canonical finite set of actually distinct centres

A heterogeneous fan may contain several constraints at exactly the
same real centre. Its graph must keep ONE old vertex for that actual
tagged centre, while retaining ALL private word occurrences attached
there. Use the finite range of the actual tagged centre map as the
marked-centre type; this avoids identifying only equal sort labels or
silently deleting different constraints belonging to one centre.

Unlike the atomic-menu shortcut, this construction does NOT assume
equal relations at repeated centres. It is consequently appropriate
for general exact presentations and arbitrary private RAW paths.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable {I : Type (max u v)}

/-- Actual tagged original real point presented by the t-th centre. -/
def taggedCentre
    (sort : I → ι) (centres : ∀ t : I, X (sort t))
    (t : I) : Sigma X :=
  ⟨sort t, centres t⟩

/-- Exactly the distinct actual tagged centres (no extra points).
Different presentations with the same real centre have one common
vertex, but their constraints remain separately indexed by I. -/
def DistinctCentres
    (sort : I → ι) (centres : ∀ t : I, X (sort t)) :=
  {c : Sigma X // c ∈ Set.range (taggedCentre sort centres)}

instance distinctCentres_finite [Finite I]
    (sort : I → ι) (centres : ∀ t : I, X (sort t)) :
    Finite (DistinctCentres sort centres) := by
  unfold DistinctCentres
  exact (Set.finite_range (taggedCentre sort centres)).to_subtype

/-- Every listed occurrence selects its literal actual centre vertex. -/
def toDistinctCentre
    (sort : I → ι) (centres : ∀ t : I, X (sort t))
    (t : I) : DistinctCentres sort centres :=
  ⟨taggedCentre sort centres t, ⟨t, rfl⟩⟩

def distinctCentreSort
    (sort : I → ι) (centres : ∀ t : I, X (sort t))
    (c : DistinctCentres sort centres) : ι :=
  c.val.1

def distinctCentrePoint
    (sort : I → ι) (centres : ∀ t : I, X (sort t))
    (c : DistinctCentres sort centres) :
    X (distinctCentreSort sort centres c) :=
  c.val.2

theorem distinctCentreTag_injective
    (sort : I → ι) (centres : ∀ t : I, X (sort t)) :
    Function.Injective
      (fun c : DistinctCentres sort centres =>
        (⟨distinctCentreSort sort centres c,
          distinctCentrePoint sort centres c⟩ : Sigma X)) := by
  intro c d h
  exact Subtype.ext h

/-- The centre of every original occurrence is literally the centre
of its canonical graph vertex, with the correct dependent sort. -/
theorem toDistinctCentre_tagged
    (sort : I → ι) (centres : ∀ t : I, X (sort t))
    (t : I) :
    (⟨distinctCentreSort sort centres (toDistinctCentre sort centres t),
      distinctCentrePoint sort centres (toDistinctCentre sort centres t)⟩ :
        Sigma X) = taggedCentre sort centres t :=
  rfl

/-- Conversely, every marked actual centre is represented by at least
one original occurrence, not an externally invented old point. -/
theorem distinctCentre_has_occurrence
    (sort : I → ι) (centres : ∀ t : I, X (sort t))
    (c : DistinctCentres sort centres) :
    ∃ t : I, toDistinctCentre sort centres t = c := by
  obtain ⟨t, ht⟩ := c.property
  refine ⟨t, ?_⟩
  apply Subtype.ext
  exact ht

end CCO.RawExact
