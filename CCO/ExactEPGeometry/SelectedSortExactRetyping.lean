import CCO.ExactEPGeometry.SelectedSortSource
import CCO.ExactCRT.ProjectedWords
import CCO.RawExact.ActualOrbitalExact

/-!
# B062 C82: first exact RAW retyping certificate for selected quotient sorts

A sort-selection subsource cannot inherit nonempty RAW exact words by
plain restriction: an old word may visit a sort deleted by selection.
Instead supply a genuine bijective, group-equivariant transport from
EACH old point sort to one retained target sort.

This file proves preservation and reflection of complete actual pair
orbitals and of individual RAW atomic letters under these transports.
Later source modules retarget ALL intermediate sorts of entire words,
including logical identity and full nonempty exact intersections.

The hypotheses are structural equivalences of ACTUAL carriers, not an
automorphism-group section and not quotient SAP. B062 instantiates
them with its already proved coherent E-class maps.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open CCO.ExactCRT

noncomputable section

variable {ι κ : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable [Fintype κ] (σ : κ ↪ ι)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- C82's true pointwise coherence for a potential old-to-selected
retyping. Every old named sort has an EQUIVARIANT EQUIVALENCE of its
entire carrier with the ACTUAL chosen retained sort carrier. -/
structure SelectedRetyping where
  target : ι → κ
  pointEquiv : ∀ i : ι, X i ≃ X (σ (target i))
  equivariant : ∀ i : ι, ∀ g : G, ∀ x : X i,
    pointEquiv i (g • x) = g • pointEquiv i x

namespace SelectedRetyping

variable {S σ} (D : SelectedRetyping (X := X) σ (G := G))

/-- Any two true B.G-orbitals are preserved and reflected by the
two FULL equivariant point equivalences; the group element is
exactly the SAME on both endpoints. -/
theorem orbital_iff
    {i j : ι} (x x' : X i) (y y' : X j) :
    GroupActions.orbital (G := G) x y x' y' ↔
      GroupActions.orbital (G := G)
        (D.pointEquiv i x) (D.pointEquiv j y)
        (D.pointEquiv i x') (D.pointEquiv j y') := by
  constructor
  · rintro ⟨g,hx,hy⟩
    refine ⟨g,?_,?_⟩
    · calc
        g • D.pointEquiv i x =
            D.pointEquiv i (g • x) := (D.equivariant i g x).symm
        _ = D.pointEquiv i x' := congrArg (D.pointEquiv i) hx
    · calc
        g • D.pointEquiv j y =
            D.pointEquiv j (g • y) := (D.equivariant j g y).symm
        _ = D.pointEquiv j y' := congrArg (D.pointEquiv j) hy
  · rintro ⟨g,hx,hy⟩
    refine ⟨g,?_,?_⟩
    · apply (D.pointEquiv i).injective
      calc
        D.pointEquiv i (g • x) =
            g • D.pointEquiv i x := D.equivariant i g x
        _ = D.pointEquiv i x' := hx
    · apply (D.pointEquiv j).injective
      calc
        D.pointEquiv j (g • y) =
            g • D.pointEquiv j y := D.equivariant j g y
        _ = D.pointEquiv j y' := hy

/-- An ORIGINAL actual atomic diversity colour is represented by
ONE genuine RAW word of the retained selected-sort source, even
when its transported quotient orbit becomes true diagonal identity.
The optional pair colour is obtained from REAL moved endpoints. -/
noncomputable def atomWord
    {i j : ι} (a : S.Atom i j) :
    RawWord (selectedSortAtomicSource S σ) (D.target i) (D.target j) := by
  let x : X i := Classical.choose (S.realized a)
  let y : X j := Classical.choose (Classical.choose_spec (S.realized a))
  exact actualPairWord (selectedSortAtomicSource S σ)
    (D.pointEquiv i x) (D.pointEquiv j y)

/-- Every whole old atomic orbital is carried to precisely the
represented new RAW letter, and back. The result includes cases
in which its new RAW word is the TRUE diagonal, not diversity. -/
theorem atomWord_iff
    (H : HomogeneousSource S G)
    {i j : ι} (a : S.Atom i j) (x : X i) (y : X j) :
    S.atomRel a x y ↔
      RawWord.relation (selectedSortAtomicSource S σ)
        (D.atomWord a) (D.pointEquiv i x) (D.pointEquiv j y) := by
  let T := selectedSortAtomicSource S σ
  letI : ∀ k : κ, MulAction G (X (σ k)) := fun k => inferInstance
  let HT : HomogeneousSource T G := selectedSortHomogeneous S σ H
  let x₀ : X i := Classical.choose (S.realized a)
  let y₀ : X j := Classical.choose (Classical.choose_spec (S.realized a))
  have hColour : S.colour x₀ y₀ = some a :=
    Classical.choose_spec (Classical.choose_spec (S.realized a))
  have hOld : S.rawAtomRel (S.colour x₀ y₀) =
      GroupActions.orbital (G := G) x₀ y₀ :=
    (RawExact.actual_pair_orbital_of_homogeneous S H x₀ y₀).symm
  have hNew : T.rawAtomRel
        (T.colour (D.pointEquiv i x₀) (D.pointEquiv j y₀)) =
      GroupActions.orbital (G := G)
        (D.pointEquiv i x₀) (D.pointEquiv j y₀) :=
    (RawExact.actual_pair_orbital_of_homogeneous T HT
      (D.pointEquiv i x₀) (D.pointEquiv j y₀)).symm
  calc
    S.atomRel a x y ↔
        S.rawAtomRel (S.colour x₀ y₀) x y := by
          rw [hColour]
          exact Iff.rfl
    _ ↔ GroupActions.orbital (G := G) x₀ y₀ x y :=
      Iff.of_eq (congrFun (congrFun hOld x) y)
    _ ↔ GroupActions.orbital (G := G)
          (D.pointEquiv i x₀) (D.pointEquiv j y₀)
          (D.pointEquiv i x) (D.pointEquiv j y) :=
      D.orbital_iff x₀ x y₀ y
    _ ↔ T.rawAtomRel
          (T.colour (D.pointEquiv i x₀) (D.pointEquiv j y₀))
          (D.pointEquiv i x) (D.pointEquiv j y) :=
      (Iff.of_eq (congrFun (congrFun hNew
        (D.pointEquiv i x)) (D.pointEquiv j y))).symm
    _ ↔ RawWord.relation T (D.atomWord a)
          (D.pointEquiv i x) (D.pointEquiv j y) := by
      unfold atomWord
      have hh := actualPairWord_relation T
        (D.pointEquiv i x₀) (D.pointEquiv j y₀)
      exact (Iff.of_eq (congrFun (congrFun hh
        (D.pointEquiv i x)) (D.pointEquiv j y))).symm

end SelectedRetyping
end
end CCO.ExactEPGeometry
