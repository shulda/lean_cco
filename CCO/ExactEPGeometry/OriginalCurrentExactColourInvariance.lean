import CCO.ExactEPGeometry.OriginalExactOccupancy

/-!
# B062 C96: original exact E membership is a genuine CURRENT pair-colour predicate

A fixed original full exact E pulls back along the REAL prefix reduct.
The source C65 theorem proves this pulled-back old E is invariant under
the actual current group B.G. Finite pair homogeneity of the actual
current source therefore makes its truth value constant on each
complete old current atomic pair colour, including logical equality.

This isolates the old E-colour transfer needed after embedding finite
fine-colour marked diagrams into the genuine AP-only marked successor.
It does NOT manufacture an action of the quotient automorphism group,
a new projected orbital palette, a quotient SAP provider, or a full
marked quotient age.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- A complete current pair orbital determines membership in the
pulled-back ORIGINAL exact equivalence E. Both implications are
proved using the real current B.G action and the genuine C65
original-prefix invariance. No reverse transport of old automorphisms
or group section is required. -/
theorem originalCurrentExactE_pairColour_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i j : B.Sorts)
    (x x' : B.Point i) (y y' : B.Point j)
    (hColour : B.source.colour x y = B.source.colour x' y') :
    (currentOriginalExactSetoid A B P base hOne E).r
      (⟨i,x⟩ : Sigma B.Point) (⟨j,y⟩ : Sigma B.Point) ↔
    (currentOriginalExactSetoid A B P base hOne E).r
      (⟨i,x'⟩ : Sigma B.Point) (⟨j,y'⟩ : Sigma B.Point) := by
  change originalExactGlobalRelation A base hOne E
      (P.project ⟨i,x⟩) (P.project ⟨j,y⟩) ↔
    originalExactGlobalRelation A base hOne E
      (P.project ⟨i,x'⟩) (P.project ⟨j,y'⟩)
  constructor
  · intro hxy
    obtain ⟨g,hgx,hgy⟩ :=
      (B.source.pair_homogeneous_of_homogeneous B.homogeneous)
        x x' y y' hColour
    have hMoved :=
      (originalExactGlobalRelation_prefix_invariant
        A B P base hOne E) g x y hxy
    simpa only [hgx,hgy] using hMoved
  · intro hxy
    obtain ⟨g,hgx,hgy⟩ :=
      (B.source.pair_homogeneous_of_homogeneous B.homogeneous)
        x' x y' y hColour.symm
    have hMoved :=
      (originalExactGlobalRelation_prefix_invariant
        A B P base hOne E) g x' y' hxy
    simpa only [hgx,hgy] using hMoved

end
end CCO.ExactEPGeometry
