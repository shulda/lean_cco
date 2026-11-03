import CCO.ExactEPGeometry.RelativeIndexQuotientTransport
import CCO.RigidGroupoid.Geometry.ProjectedKernels

/-!
# B062 C105: the full equivalence lattice above a literal quotient kernel

Unlike the full-exact quotient lemmas, terminality concerns ANY invariant
equivalences, including ones without RAW exact presentations. This
generic setoid argument does not require any exactness or SAP.

For a SURJECTIVE quotient map pi, every equivalence F containing
its actual fibre kernel descends to a genuine equivalence on the
quotient. Pulling it back gives precisely F. Conversely every
quotient equivalence pulls back, and projecting it again gives
itself. These are genuine whole-pair statements, not a quotient
of only the RAW-exact sublattice. Invariance under the actual group
action is a subsequent source-specific application of equivariance.
-/

universe u v

namespace CCO.ExactEPGeometry

noncomputable section

/-- A FULL arbitrary equivalence relation F descends along any
surjective map whose kernel is contained in F. No exactness or
invariant-orbital presentation is necessary for the setoid itself. -/
noncomputable def fullSetoidProjection
    {X : Type u} {Y : Type v}
    (pi : X → Y) (onto : Function.Surjective pi)
    (F : Setoid X)
    (hKernel : ∀ x y, pi x = pi y → F x y) : Setoid Y where
  r := Quotient.image pi pi F.r
  iseqv := ⟨
    (by
      intro q
      obtain ⟨x,rfl⟩ := onto q
      exact ⟨x,x,rfl,rfl,F.refl x⟩),
    (by
      rintro q r ⟨x,y,hx,hy,hxy⟩
      exact ⟨y,x,hy,hx,F.symm hxy⟩),
    (by
      rintro q r s ⟨x,y,hx,hy,hxy⟩
        ⟨y',z,hy',hz,hy'z⟩
      exact ⟨x,z,hx,hz,
        F.trans hxy (F.trans
          (hKernel y y' (hy.trans hy'.symm)) hy'z)⟩)
  ⟩

/-- The projected FULL equivalence has exactly its original
inverse image. No quotient automorphism section is involved. -/
theorem fullSetoidProjection_pullback_iff
    {X : Type u} {Y : Type v}
    (pi : X → Y) (onto : Function.Surjective pi)
    (F : Setoid X)
    (hKernel : ∀ x y, pi x = pi y → F x y)
    (x y : X) :
    (fullSetoidProjection pi onto F hKernel) (pi x) (pi y) ↔
      F x y := by
  constructor
  · rintro ⟨a,b,ha,hb,hab⟩
    exact F.trans (hKernel x a ha.symm)
      (F.trans hab (hKernel b y hb))
  · intro hxy
    exact ⟨x,y,rfl,rfl,hxy⟩

/-- Any original FULL equivalence above the actual quotient kernel
is recovered exactly. This extends beyond the RAW exact interval. -/
theorem fullSetoidProjection_comap_eq
    {X : Type u} {Y : Type v}
    (pi : X → Y) (onto : Function.Surjective pi)
    (F : Setoid X)
    (hKernel : ∀ x y, pi x = pi y → F x y) :
    Setoid.comap pi (fullSetoidProjection pi onto F hKernel) = F := by
  apply Setoid.ext
  intro x y
  exact fullSetoidProjection_pullback_iff pi onto F hKernel x y

/-- Projecting a genuine pullback FULL equivalence recovers exactly
the original quotient equivalence, on ALL pairs. -/
theorem fullSetoidProjection_comap_inverse
    {X : Type u} {Y : Type v}
    (pi : X → Y) (onto : Function.Surjective pi)
    (F : Setoid Y) :
    fullSetoidProjection pi onto (Setoid.comap pi F)
      (fun x y h => by
        change F (pi x) (pi y)
        rw [h]
        exact F.refl (pi y)) = F := by
  apply Setoid.ext
  intro q r
  constructor
  · rintro ⟨x,y,hx,hy,hxy⟩
    change F (pi x) (pi y) at hxy
    simpa only [hx,hy] using hxy
  · intro hqr
    obtain ⟨x,hx⟩ := onto q
    obtain ⟨y,hy⟩ := onto r
    exact ⟨x,y,hx,hy,(by simpa only [hx,hy] using hqr)⟩

/-- Projected FULL equivalences preserve inclusion, provided both
really contain the fibre kernel. No RAW exactness enters. -/
theorem fullSetoidProjection_mono
    {X : Type u} {Y : Type v}
    (pi : X → Y) (onto : Function.Surjective pi)
    (F G : Setoid X)
    (hF : ∀ x y, pi x = pi y → F x y)
    (hG : ∀ x y, pi x = pi y → G x y)
    (hFG : F ≤ G) :
    fullSetoidProjection pi onto F hF ≤
      fullSetoidProjection pi onto G hG := by
  intro q r h
  obtain ⟨x,y,hx,hy,hxy⟩ := h
  exact ⟨x,y,hx,hy,hFG hxy⟩

end
end CCO.ExactEPGeometry
