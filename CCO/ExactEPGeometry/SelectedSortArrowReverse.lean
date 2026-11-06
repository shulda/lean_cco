import CCO.ExactEPGeometry.SelectedSortExactArrows
import CCO.RigidGroupoid.Geometry.QuotientBijection

/-!
# B062 C83: FULL reverse transport of the genuine selected-sort groupoid

Forward transport already preserves exact RAW presentations, the four
Arrow laws and composition, and is faithful. To prove its SURJECTIVITY,
start with an ARBITRARY whole full-exact Arrow of the selected source.

By actual homogeneous rectangularity it is the composite of its two
real transported endpoint gates and ONE actual selected pair orbital.
The selected pair is transported back to two genuine original points.
Equivariance identifies its entire selected pair orbital with the
transport of the original actual atomic pair orbital. The source
AP+HOM-CCO exact calculus proves the resulting full old rectangle is
RAW exact; the four old Arrow laws follow by faithful relation
transport from the actual target Arrow laws. Thus every target full
Arrow has a REAL original Arrow preimage, with no arbitrary reverse
RAW-word descent or quotient SAP, no action section, and no preferred
generator or single orbit in place of the full Hom set.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry

noncomputable section

variable {ι κ : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable [Fintype κ] {σ : κ ↪ ι}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (D : SelectedRetyping (X := X) σ (G := G))

namespace SelectedRetyping

/-- Bijective carrier retyping is faithful on the WHOLE represented
binary relation, not merely on a selected exact subfamily. -/
theorem transportRelation_injective {i j : ι} :
    Function.Injective (fun R : TRel X i j => D.transportRelation R) := by
  intro R U h
  funext x y
  have hh := congrFun (congrFun h (D.pointEquiv i x))
    (D.pointEquiv j y)
  change D.transportRelation R (D.pointEquiv i x)
      (D.pointEquiv j y) =
    D.transportRelation U (D.pointEquiv i x)
      (D.pointEquiv j y) at hh
  change R x y = U x y
  simpa only [transportRelation, Equiv.symm_apply_apply] using hh

/-- The entire actual selected pair orbital is the transported
genuine original pair orbital. This includes the equality case,
which is true diagonal rather than a fictitious diversity letter. -/
theorem transportRelation_actual_pair
    (H : HomogeneousSource S G)
    {i j : ι} (x : X i) (y : X j) :
    D.transportRelation (S.rawAtomRel (S.colour x y)) =
      (selectedSortAtomicSource S σ).rawAtomRel
        ((selectedSortAtomicSource S σ).colour
          (D.pointEquiv i x) (D.pointEquiv j y)) := by
  let T := selectedSortAtomicSource S σ
  letI : ∀ k : κ, MulAction G (X (σ k)) := fun k => inferInstance
  let HT : HomogeneousSource T G := selectedSortHomogeneous S σ H
  have hOld : S.rawAtomRel (S.colour x y) =
      GroupActions.orbital (G := G) x y :=
    (RawExact.actual_pair_orbital_of_homogeneous S H x y).symm
  have hNew : T.rawAtomRel
        (T.colour (D.pointEquiv i x) (D.pointEquiv j y)) =
      GroupActions.orbital (G := G)
        (D.pointEquiv i x) (D.pointEquiv j y) :=
    (RawExact.actual_pair_orbital_of_homogeneous T HT
      (D.pointEquiv i x) (D.pointEquiv j y)).symm
  funext a b
  apply propext
  change S.rawAtomRel (S.colour x y)
      ((D.pointEquiv i).symm a) ((D.pointEquiv j).symm b) ↔
    T.rawAtomRel (T.colour (D.pointEquiv i x)
      (D.pointEquiv j y)) a b
  rw [hOld, hNew]
  simpa only [Equiv.apply_symm_apply] using
    (D.orbital_iff x ((D.pointEquiv i).symm a)
      y ((D.pointEquiv j).symm b))

/-- C83 genuine whole-Hom SURJECTIVITY: each complete selected Arrow
between the actual transported endpoint gates is the image of ONE
complete original Arrow. Its witness is the old gate--atom--gate
rectangle selected from an ACTUAL target pair, not a postulated
reverse exactness of arbitrary quotient words. -/
theorem transportArrow_surjective
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (Kp : Kernel S i) (Kq : Kernel S j) :
    Function.Surjective
      (fun R : Arrow S Kp Kq => D.transportArrow H R) := by
  intro U
  let T := selectedSortAtomicSource S σ
  letI : ∀ k : κ, MulAction G (X (σ k)) := fun k => inferInstance
  let HT : HomogeneousSource T G := selectedSortHomogeneous S σ H
  obtain ⟨a,b,hab⟩ := U.exact.nonempty T
  let x : X i := (D.pointEquiv i).symm a
  let y : X j := (D.pointEquiv j).symm b
  let R : TRel X i j :=
    TRel.comp (TRel.comp Kp.rel (S.rawAtomRel (S.colour x y))) Kq.rel
  let C : ExactCalculus S := exactCalculus_of_homogeneous_CCO S H cco
  have hExact : FullExact S R :=
    C.comp (C.comp Kp.exact (fullExact_actual_atom S x y)) Kq.exact
  have hTransport : D.transportRelation R = U.rel := by
    calc
      D.transportRelation R =
          TRel.comp
            (TRel.comp (D.transportRelation Kp.rel)
              (D.transportRelation (S.rawAtomRel (S.colour x y))))
            (D.transportRelation Kq.rel) := by
              dsimp only [R]
              rw [D.transportRelation_comp, D.transportRelation_comp]
      _ = TRel.comp
            (TRel.comp (D.transportKernel H Kp).rel
              (T.rawAtomRel (T.colour a b)))
            (D.transportKernel H Kq).rel := by
              rw [D.transportRelation_actual_pair H x y]
              dsimp only [T]
              simp only [x,y,Equiv.apply_symm_apply]
              all_goals rfl
      _ = U.rel := by
              have h := U.rectangular HT hab
              exact h.symm
  have hLeft : TRel.comp Kp.rel R = R := by
    apply D.transportRelation_injective
    change D.transportRelation (TRel.comp Kp.rel R) =
      D.transportRelation R
    rw [D.transportRelation_comp]
    change TRel.comp (D.transportKernel H Kp).rel
      (D.transportRelation R) = D.transportRelation R
    rw [hTransport, U.left]
  have hRight : TRel.comp R Kq.rel = R := by
    apply D.transportRelation_injective
    change D.transportRelation (TRel.comp R Kq.rel) =
      D.transportRelation R
    rw [D.transportRelation_comp]
    change TRel.comp (D.transportRelation R)
      (D.transportKernel H Kq).rel = D.transportRelation R
    rw [hTransport, U.right]
  have hSource : TRel.comp R (TRel.converse R) = Kp.rel := by
    apply D.transportRelation_injective
    change D.transportRelation (TRel.comp R (TRel.converse R)) =
      D.transportRelation Kp.rel
    rw [D.transportRelation_comp, D.transportRelation_converse]
    change TRel.comp (D.transportRelation R)
      (TRel.converse (D.transportRelation R)) =
        (D.transportKernel H Kp).rel
    rw [hTransport, U.source]
  have hTarget : TRel.comp (TRel.converse R) R = Kq.rel := by
    apply D.transportRelation_injective
    change D.transportRelation (TRel.comp (TRel.converse R) R) =
      D.transportRelation Kq.rel
    rw [D.transportRelation_comp, D.transportRelation_converse]
    change TRel.comp (TRel.converse (D.transportRelation R))
      (D.transportRelation R) =
        (D.transportKernel H Kq).rel
    rw [hTransport, U.target]
  let V : Arrow S Kp Kq := {
    rel := R
    exact := hExact
    left := hLeft
    right := hRight
    source := hSource
    target := hTarget
  }
  refine ⟨V,?_⟩
  apply Arrow.ext
  change D.transportRelation R = U.rel
  exact hTransport

/-- C83 full equivalence on ALL actual whole exact Arrow Hom sets,
not just one selected orbital or a conditional projected-gate
provider. The source AP/HOM-CCO is used for real old rectangular
exactness; every target full Arrow supplies its own real witness. -/
noncomputable def transportArrowEquiv
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j : ι} (Kp : Kernel S i) (Kq : Kernel S j) :
    Arrow S Kp Kq ≃ Arrow (selectedSortAtomicSource S σ)
      (D.transportKernel H Kp) (D.transportKernel H Kq) :=
  Equiv.ofBijective (fun R => D.transportArrow H R)
    ⟨D.transportArrow_injective H,
      D.transportArrow_surjective H cco Kp Kq⟩

end SelectedRetyping
end
end CCO.ExactEPGeometry
