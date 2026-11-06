import CCO.ExactEPGeometry.CertifiedHistoryMaximality
import CCO.ExactEPGeometry.ActualPrefixSupport

/-!
# B062 C65: real ORIGINAL exact E-classes and actual prefix-type occupancy

Fix one genuine ORIGINAL homogeneous symmetric AP+HOM-CCO source
with its ONE original sort, an ORIGINAL full RAW-exact equivalence E
(including Id or Top), and a real current homogeneous unary prefix.

The old exact E becomes a literal equivalence on tagged original
points and, through the ACTUAL full-carrier reduct bijection, a
setoid on the WHOLE real current tagged carrier. No quotient points
or automorphism-group sections are postulated.

Old exactness and one-original-sort equality give the needed typed
original invariant relations. The current source's actual old-colour
projection and both genuine source homogeneities then prove E is
invariant under current automorphisms. Consequently its support on
real current unary type names is a true equivalence and EVERY real
E-class meeting one type meets ALL its supported types, by the
previously proved N06 occupancy lemma.

This is the semantic C65 foundation, not yet construction of the
new named-sorted quotient AtomicSource or quotient-tower step.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Original full RAW-exact E is a genuine equivalence on ALL
tagged ORIGINAL points, with the unique old carrier identified only
by literal equalities of original sort names. -/
theorem originalExactGlobalRelation_equiv
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    RawSymmetric.EquivRel (originalExactGlobalRelation A base hOne E) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨i,x⟩
    exact E.val.val.refl _
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    exact E.val.val.symm h
  · rintro ⟨i,x⟩ ⟨j,y⟩ ⟨k,z⟩ hxy hyz
    exact E.val.val.trans hxy hyz

/-- The ORIGINAL exact global E is invariant under the actual old
source group action even if the one original sort has not been
definitionally presented as Unit. The casts are along ACTUAL
original sort equalities, not a new representation. -/
theorem originalExactGlobalRelation_typed_invariant
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    ∀ i j : A.Sorts,
      TRel.Invariant (G := A.G)
        (fun x : A.Point i => fun y : A.Point j =>
          E ((hOne i).symm ▸ x) ((hOne j).symm ▸ y)) := by
  intro i j
  cases hOne i
  cases hOne j
  exact E.property.invariant A.source A.homogeneous

/-- Proved current group invariance of ORIGINAL E after the actual
unary projection. No global current/old group homomorphism or
quotient automorphism-group section is supplied or required. -/
theorem originalExactGlobalRelation_prefix_invariant
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    PrefixInvariant (K := B.G) P
      (originalExactGlobalRelation A base hOne E) := by
  have hTyped := originalExactGlobalRelation_typed_invariant
    A base hOne E
  have hGlobal : PrefixInvariant (K := B.G) P
      (globalRelation
        (fun (i j : A.Sorts) (x : A.Point i) (y : A.Point j) =>
          E ((hOne i).symm ▸ x) ((hOne j).symm ▸ y))) :=
    globalRelation_prefix_invariant
      (G := A.G) (K := B.G)
      A.homogeneous B.homogeneous P
      (fun i j x y => E ((hOne i).symm ▸ x) ((hOne j).symm ▸ y))
      hTyped
  intro i j g x y hxy
  exact hGlobal (i := i) (j := j) g x y hxy

/-- The real current full-carrier E relation, as a genuine setoid
on the actual tagged current points. Its classes are literal E-classes,
not independent arbitrary quotients of each current named sort. -/
def currentOriginalExactSetoid
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) : Setoid (Sigma B.Point) := by
  let hEq := originalExactGlobalRelation_equiv A base hOne E
  exact {
    r := fun a b =>
      originalExactGlobalRelation A base hOne E (P.project a) (P.project b)
    iseqv := ⟨
      fun a => hEq.refl (P.project a),
      (by intro a b hab; exact hEq.symm _ _ hab),
      (by intro a b c hab hbc; exact hEq.trans _ _ _ hab hbc)⟩
  }

/-- The actual supported types of ORIGINAL exact E form a
genuine equivalence on the whole finite CURRENT unary type set,
including all named sorts, not only a list of realized colours. -/
theorem originalExactTypeSupport_equiv
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    RawSymmetric.EquivRel
      (prefixSupport P (originalExactGlobalRelation A base hOne E)) :=
  prefixSupport_equivalence P B.homogeneous
    (originalExactGlobalRelation A base hOne E)
    (originalExactGlobalRelation_equiv A base hOne E)
    (originalExactGlobalRelation_prefix_invariant A B P base hOne E)

/-- Source C65 occupancy for EACH individual actual E-class:
a displayed supported type j contains a real point in the SAME
old E-class as ANY specified real current point x of type i.
It is not an existential statement about some unrelated E-class. -/
theorem originalExactClass_occupies_supported_type
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i j : B.Sorts) (x : B.Point i) :
    prefixSupport P (originalExactGlobalRelation A base hOne E) i j ↔
      ∃ y : B.Point j,
        (currentOriginalExactSetoid A B P base hOne E).r
          (⟨i,x⟩ : Sigma B.Point) (⟨j,y⟩ : Sigma B.Point) :=
  prefixSupport_occupancy P B.homogeneous
    (originalExactGlobalRelation A base hOne E)
    (originalExactGlobalRelation_prefix_invariant A B P base hOne E)
    i j x

end
end CCO.ExactEPGeometry
