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

universe u v w t z

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


/-- True old E-class equality is determined by the COMPLETE TAGGED
current pair colour, not just by an untyped colour name. This
includes mixed old named sorts and the genuine logical diagonal. -/
theorem originalCurrentExactE_taggedColour_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (p q p' q' : Sigma B.Point)
    (hColour : taggedColour B.source p q =
      taggedColour B.source p' q') :
    (currentOriginalExactSetoid A B P base hOne E).r p q ↔
      (currentOriginalExactSetoid A B P base hOne E).r p' q' := by
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  rcases p' with ⟨k,x'⟩
  rcases q' with ⟨l,y'⟩
  have hi : i = k :=
    congrArg (fun a : Σ i : B.Sorts,
      Σ j : B.Sorts, Option (B.source.Atom i j) => a.1) hColour
  have hj : j = l :=
    congrArg (fun a : Σ i : B.Sorts,
      Σ j : B.Sorts, Option (B.source.Atom i j) => a.2.1) hColour
  cases hi
  cases hj
  have hc : B.source.colour x y = B.source.colour x' y' := by
    simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and]
      using hColour
  exact originalCurrentExactE_pairColour_iff
    A B P base hOne E i j x x' y y' hc

/-- Any indexed fine old pair-colour chart, simultaneously on ALL
its vertex pairs, preserves and reflects original E-class equality.
In particular it preserves inequality of distinct original E-classes.
No quotient SAP or new quotient orbital naming is used. -/
theorem originalCurrentExactE_fullColourChart_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {V : Type z} (old new : V → Sigma B.Point)
    (hColours : ∀ i j : V, taggedColour B.source (old i) (old j) =
      taggedColour B.source (new i) (new j)) :
    ∀ i j : V,
      (currentOriginalExactSetoid A B P base hOne E).r
        (old i) (old j) ↔
      (currentOriginalExactSetoid A B P base hOne E).r
        (new i) (new j) := by
  intro i j
  exact originalCurrentExactE_taggedColour_iff
    A B P base hOne E (old i) (old j)
      (new i) (new j) (hColours i j)

end
end CCO.ExactEPGeometry
