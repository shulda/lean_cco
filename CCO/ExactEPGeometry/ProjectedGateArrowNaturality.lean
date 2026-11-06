import CCO.ExactEPGeometry.ProjectedGateClassEquiv
import CCO.RigidGroupoid.Geometry.QuotientBijection

/-!
# B062 C83/C93: naturality of K-class equivalences for full projected Arrows

For genuine exact gates Kp, Kq containing the actual quotient kernels,
the class equivalences K ≃ K/E are natural under EVERY real full Arrow
whose projected complete relation contains the image of the old Arrow.
The displayed projection equality is proved by choosing the actual
pointImage witness of the full Arrow and using quotientMap_eq_iff.
No source automorphism-group section, SAP, arbitrary mixed reverse
descent or generator-only condition is used.

The receiving B062 application must instantiate the projected Arrows
and their image law from its actual C82/C83 selected quotient source;
this generic lemma does not assert such a source is automatic.
-/

universe u v w q r t s

namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry

noncomputable section

variable {ι : Type u} {X : ι → Type v} {Y : ι → Type q}
variable {S : AtomicSource.{u,v,w} ι X}
variable {T : AtomicSource.{u,q,r} ι Y}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {G' : Type s} [Group G'] [∀ i, MulAction G' (Y i)]
variable (H : HomogeneousSource S G) (HT : HomogeneousSource T G')
variable {i j : ι} (Kp : Kernel S i) (Kq : Kernel S j)
variable (pi : X i → Y i) (sigma : X j → Y j)
variable (surjPi : Function.Surjective pi)
variable (surjSigma : Function.Surjective sigma)
variable (hNestedPi : ∀ x y, pi x = pi y → Kp.rel x y)
variable (hNestedSigma : ∀ x y, sigma x = sigma y → Kq.rel x y)

/-- An actual full Arrow commutes with the literal class maps
Kp→Kp/E and Kq→Kq/E, provided its actual projected Arrow has
the proved image-membership law on ALL old real pairs. No
inverse-image exactness is asserted here. -/
theorem projectedGateClassMap_arrow_natural
    (hExactP : FullExact T
      (Kp.projectedSetoid pi surjPi hNestedPi).r)
    (hExactQ : FullExact T
      (Kq.projectedSetoid sigma surjSigma hNestedSigma).r)
    (R : Arrow S Kp Kq)
    (U : Arrow T
      (Kp.projectedKernel T pi surjPi hNestedPi hExactP)
      (Kq.projectedKernel T sigma surjSigma hNestedSigma hExactQ))
    (hImage : ∀ x y, R.rel x y → U.rel (pi x) (sigma y)) :
    ∀ p : Kp.Class,
      projectedGateClassMap Kq sigma surjSigma hNestedSigma
        (R.quotientMap H p) =
      U.quotientMap HT
        (projectedGateClassMap Kp pi surjPi hNestedPi p) := by
  intro p
  induction p using Quotient.inductionOn with
  | _ x =>
    let y := R.pointImage H x
    have hR : R.rel x y := R.pointImage_spec H x
    have hU : U.rel (pi x) (sigma y) := hImage x y hR
    have hQuotient :
        U.quotientMap HT
          ((Kp.projectedKernel T pi surjPi hNestedPi hExactP).project (pi x)) =
        (Kq.projectedKernel T sigma surjSigma hNestedSigma hExactQ).project
          (sigma y) :=
      (U.quotientMap_eq_iff HT (pi x) (sigma y)).mpr hU
    change U.quotientMap HT (Quotient.mk'' (pi x)) =
      Quotient.mk'' (sigma y) at hQuotient
    change projectedGateClassMap Kq sigma surjSigma hNestedSigma
        (R.quotientMap H (Kp.project x)) =
      U.quotientMap HT
        (projectedGateClassMap Kp pi surjPi hNestedPi (Kp.project x))
    rw [R.quotientMap_project H x]
    change Quotient.mk'' (sigma y) =
      U.quotientMap HT (Quotient.mk'' (pi x))
    exact hQuotient.symm

end
end CCO.ExactEPGeometry
