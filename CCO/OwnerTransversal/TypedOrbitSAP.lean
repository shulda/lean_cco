import CCO.Stabilizer
import CCO.AclOwners.Avoidance
import CCO.RawExact.QuotientAgeAP

/-! Generic finite-age SAP from actual infinite stabilizer orbits.
One group element moves the entire off-base finite factor at once. -/
universe u v w t
namespace CCO.OwnerTransversal
open RealAction
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [MulAction G (Sigma X)]

theorem ageSAP_of_infinite_stabilizer_orbits (H : HomogeneousSource S G)
    (hInfinite : ∀ (C : FiniteInduced (X := X)) (x : Sigma X), x ∉ C.vertices →
      (RealAction.orbitOver (G := G) C.vertices x).Infinite) : AgeSAP S := by
  classical
  refine ⟨?_⟩
  intro C A B eCA eCB
  letI : Finite ↥C.vertices := C.finite_vertices.to_subtype
  let src : ↥C.vertices → Sigma X := fun c => (eCA.toEmbedding c).val
  let dst : ↥C.vertices → Sigma X := fun c => (eCB.toEmbedding c).val
  obtain ⟨g₀,hg₀⟩ := H.extends_finite_diagram src dst
    (fun c d => (eCA.preserves_colours c d).symm.trans (eCB.preserves_colours c d))
  let C' : FiniteInduced (X := X) := {
    vertices := dst '' (Set.univ : Set ↥C.vertices)
    finite_vertices := Set.finite_univ.image dst }
  let movingSet : Set (Sigma X) := ((fun a => g₀ • a) '' A.vertices) \ C'.vertices
  have movingFinite : movingSet.Finite := (A.finite_vertices.image _).sdiff
  let moving := movingFinite.toFinset
  let forbidden := B.finite_vertices.toFinset
  let K := RealAction.pointwiseStabilizer (G := G) C'.vertices
  have hOrbit (a : Sigma X) (ha : a ∈ moving) : (MulAction.orbit K a).Infinite := by
    have ha' := movingFinite.mem_toFinset.mp ha
    apply (hInfinite C' a ha'.2).mono
    rintro b ⟨g,hg,hgb⟩
    exact MulAction.mem_orbit_iff.mpr ⟨⟨g,hg⟩,hgb⟩
  obtain ⟨k,hk⟩ := AclOwners.finite_action_avoidance (G := K) moving forbidden hOrbit
  let g : G := k.val * g₀
  have hBase (c : ↥C.vertices) : g • (eCA.toEmbedding c).val = (eCB.toEmbedding c).val := by
    change (k.val * g₀) • src c = dst c
    rw [mul_smul,hg₀]
    exact k.property (dst c) ⟨c,Set.mem_univ _,rfl⟩
  let D : FiniteInduced (X := X) := {
    vertices := (fun a => g • a) '' A.vertices ∪ B.vertices
    finite_vertices := (A.finite_vertices.image _).union B.finite_vertices }
  let eAD : InducedEmbedding S A D := {
    toEmbedding := {
      toFun := fun a => ⟨g • a.val,Or.inl ⟨a.val,a.property,rfl⟩⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        have hh := congrArg (fun p : ↥D.vertices => g⁻¹ • p.val) hab
        simpa only [inv_smul_smul] using hh }
    preserves_sort := fun a => H.preserves_sort g a.val
    preserves_colours := fun a b => (H.preserves_colours g a.val b.val).symm }
  let eBD : InducedEmbedding S B D := {
    toEmbedding := {
      toFun := fun b => ⟨b.val,Or.inr b.property⟩
      inj' := fun a b hab => Subtype.ext (congrArg (fun p : ↥D.vertices => p.val) hab) }
    preserves_sort := fun _ => rfl
    preserves_colours := fun _ _ => rfl }
  refine ⟨D,eAD,eBD,?_,?_⟩
  · intro c
    exact Subtype.ext (hBase c)
  · intro a b hab
    have hValue : g • a.val = b.val := congrArg Subtype.val hab
    have hIn : g₀ • a.val ∈ C'.vertices := by
      by_contra hnot
      have hMoving : g₀ • a.val ∈ moving := movingFinite.mem_toFinset.mpr
        ⟨⟨a.val,a.property,rfl⟩,hnot⟩
      exact hk (g₀ • a.val) hMoving b.val (B.finite_vertices.mem_toFinset.mpr b.property)
        (by change k.val • (g₀ • a.val) = b.val; simpa only [g,mul_smul] using hValue)
    obtain ⟨c,_,hc⟩ := hIn
    have hCA : eCA.toEmbedding c = a := by
      apply Subtype.ext
      have hh : g₀ • (eCA.toEmbedding c).val = g₀ • a.val := (hg₀ c).trans hc
      have hi := congrArg (fun p : Sigma X => g₀⁻¹ • p) hh
      simpa only [inv_smul_smul] using hi
    refine ⟨c,hCA,?_⟩
    apply Subtype.ext
    have hh := hBase c
    rw [hCA] at hh
    exact hh.symm.trans hValue

end CCO.OwnerTransversal
