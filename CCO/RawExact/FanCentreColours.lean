import CCO.RawExact.FanFullEdgeSemantics
import CCO.RawExact.AtomicFans
import Mathlib.Tactic

/-!
# B002 C13: the full private fan really keeps the old centre diagram

The private full-fan graph contains EVERY genuine old diversity atom
between different actual tagged centres, not just their sort labels.
Thus any old-source homomorphism of the completed fan maps these
marked old centres to a finite tuple with exactly the same complete
original pair colours, including the actual logical diagonal.

One original ambient automorphism can subsequently move ALL these
marked images back to their LITERAL old real centre values. Neither
SAP nor quotient-sort homogeneity is assumed.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- The reference map on a marked centre returns that EXACT actual
old original point, not some arbitrary representative of its sort. -/
theorem privateFanNonrootTypedPoint_centre
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (c : DistinctCentres sort centres) :
    privateFanNonrootTypedPoint S H D centres
      (privateFanCentre S D centres c) =
        distinctCentrePoint sort centres c := by
  have hTag := privateFanNonrootTypedPoint_tag S H D centres
    (privateFanCentre S D centres c)
  rw [privateFanNonrootReference_centre S H D centres c] at hTag
  simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hTag

/-- Every distinct actual marked-centre pair has exactly its
original old atomic colour in the FULL, not merely punctured,
private-word fan's recorded source diagram. -/
theorem privateFanFull_centre_edge_original
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (c d : DistinctCentres sort centres)
    (hcd : c ≠ d) :
    (privateFanFullDiagram S H D centres).edge
      (privateFanCentre S D centres c)
      (privateFanCentre S D centres d)
      (privateFanCentre_injective S D centres).ne hcd =
        S.colour
          (distinctCentrePoint sort centres c)
          (distinctCentrePoint sort centres d) := by
  have hv : privateFanCentre S D centres c ≠
      privateFanRoot S D centres := by
    exact (privateFanRoot_ne_centre S D centres c).symm
  have hw : privateFanCentre S D centres d ≠
      privateFanRoot S D centres := by
    exact (privateFanRoot_ne_centre S D centres d).symm
  rw [privateFanFull_nonroot_edge_eq S H D centres
    (privateFanCentre S D centres c)
    (privateFanCentre S D centres d)
    hv hw ((privateFanCentre_injective S D centres).ne hcd)]
  have hPunct : privateFanPuncturedAdjacent S D centres
      (privateFanCentre S D centres c)
      (privateFanCentre S D centres d) :=
    ⟨hv, hw, privateFan_centres_adjacent S D centres c d hcd⟩
  change
    (if h : privateFanPuncturedAdjacent S D centres
        (privateFanCentre S D centres c)
        (privateFanCentre S D centres d) then
      S.colour
        (privateFanNonrootTypedPoint S H D centres
          (privateFanCentre S D centres c))
        (privateFanNonrootTypedPoint S H D centres
          (privateFanCentre S D centres d))
    else none) =
      S.colour
        (distinctCentrePoint sort centres c)
        (distinctCentrePoint sort centres d)
  rw [dif_pos hPunct,
    privateFanNonrootTypedPoint_centre S H D centres c,
    privateFanNonrootTypedPoint_centre S H D centres d]

/-- Any source homomorphism of the FULL private fan sends the
actual marked-centre tuple to one with ALL the same genuine old
pair colours. The diagonal case also uses literal same-centre
equality, so no injectivity was assumed rather than proved. -/
theorem privateFanFullHom_centre_colours
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (f : DiagramHom (privateFanFullDiagram S H D centres))
    (c d : DistinctCentres sort centres) :
    S.colour
      (f.point (privateFanCentre S D centres c))
      (f.point (privateFanCentre S D centres d)) =
    S.colour
      (distinctCentrePoint sort centres c)
      (distinctCentrePoint sort centres d) := by
  by_cases h : c = d
  · subst d
    have hLeft : S.colour
        (f.point (privateFanCentre S D centres c))
        (f.point (privateFanCentre S D centres c)) = none :=
      (S.colour_none_iff _ _).mpr rfl
    have hRight : S.colour
        (distinctCentrePoint sort centres c)
        (distinctCentrePoint sort centres c) = none :=
      (S.colour_none_iff _ _).mpr rfl
    exact hLeft.trans hRight.symm
  · have hDifferent : c.val ≠ d.val := by
      intro hVal
      exact h (Subtype.ext hVal)
    cases hOld : S.colour
      (distinctCentrePoint sort centres c)
      (distinctCentrePoint sort centres d) with
    | none =>
        exact False.elim (hDifferent
          ((S.colour_none_iff _ _).mp hOld))
    | some a =>
        have hEdge :
            (privateFanFullDiagram S H D centres).edge
              (privateFanCentre S D centres c)
              (privateFanCentre S D centres d)
              ((privateFanCentre_injective S D centres).ne h) =
                some a := by
          rw [privateFanFull_centre_edge_original S H D centres c d h]
          exact hOld
        exact f.preserves_edge
          (privateFanCentre S D centres c)
          (privateFanCentre S D centres d)
          ((privateFanCentre_injective S D centres).ne h)
          a hEdge

/-- Exactly ONE original source automorphism simultaneously moves
the entire completed finite old-centre diagram back to its literal
actual old centre points. Repeated original sort labels and marked
centres are handled by the canonical type of distinct tagged values. -/
theorem privateFanFullHom_align_all_centres
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (f : DiagramHom (privateFanFullDiagram S H D centres)) :
    ∃ g : G, ∀ c : DistinctCentres sort centres,
      g • f.point (privateFanCentre S D centres c) =
        distinctCentrePoint sort centres c := by
  exact align_actual_centres S H
    (distinctCentreSort sort centres)
    (fun c => f.point (privateFanCentre S D centres c))
    (distinctCentrePoint sort centres)
    (privateFanFullHom_centre_colours S H D centres f)


end CCO.RawExact
