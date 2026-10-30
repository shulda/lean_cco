import CCO.PointGeneratedSAP.Examples.Matching
import CCO.PointGeneratedSAP.Source

/-! The generic criterion is instantiated with the ACTUAL full automorphism
of the original pure real set and the literal matching interpretation. -/
namespace CCO.PointGeneratedSAP.Examples.Matching
open UnaryFreshFrames

abbrev original : Original language Point model where
  realSort b := b = false
  originalRel := ∅

def realEquiv : original.Real ≃ ℕ where
  toFun x := x.val.2
  invFun n := ⟨real n,rfl⟩
  left_inv := by
    rintro ⟨⟨b,n⟩,h⟩
    change b = false at h
    subst b
    rfl
  right_inv _ := rfl

theorem real_value (x : original.Real) : real (realEquiv x) = x.val := by
  apply Prod.ext
  · exact x.property.symm
  · rfl

def ofPerm (p : Equiv.Perm ℕ) : original.Aut := by
  refine ⟨(realEquiv.trans p).trans realEquiv.symm,?_,?_⟩
  · intro x
    exact (show model.sort (((realEquiv.trans p).trans realEquiv.symm) x).val = false from rfl).trans x.property.symm
  · intro R
    exact Empty.elim R

def toPerm (g : original.Aut) : Equiv.Perm ℕ :=
  (realEquiv.symm.trans g.val).trans realEquiv

def lift : original.Aut →* model.Aut where
  toFun g := permAut (toPerm g)
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨b,n⟩
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply Equiv.ext
    rintro ⟨b,n⟩
    change (b,(g • (h • (realEquiv.symm n))).val.2) =
      (b,(g • (realEquiv.symm ((h • realEquiv.symm n).val.2))).val.2)
    have he : realEquiv.symm ((h • realEquiv.symm n).val.2) = h • realEquiv.symm n :=
      realEquiv.left_inv (h • realEquiv.symm n)
    rw [he]

theorem lift_ofPerm (p : Equiv.Perm ℕ) : lift (ofPerm p) = permAut p := by
  apply Subtype.ext
  apply Equiv.ext
  rintro ⟨b,n⟩
  rfl

theorem real_image (D : Set original.Real) :
    Subtype.val '' D = real '' (realEquiv '' D) := by
  ext x
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact ⟨realEquiv r,⟨r,hr,rfl⟩,real_value r⟩
  · rintro ⟨n,⟨r,hr,rfl⟩,rfl⟩
    exact ⟨r,hr,(real_value r).symm⟩

def interpretation : Interpretation model original where
  lift := lift
  lift_real := by
    intro g x
    have he : x = realEquiv.symm (realEquiv x) := (realEquiv.left_inv x).symm
    rw [he]
    apply Prod.ext
    · exact (g • realEquiv.symm (realEquiv x)).property.symm
    · rfl
  locallyFinite := by
    intro D hD
    rw [real_image]
    exact closure_reals_finite (hD.image realEquiv)
  generating := by
    rintro ⟨b,n⟩
    refine ⟨⟨real n,rfl⟩,?_⟩
    cases b
    · exact model.subset_closure _ rfl
    · exact model.closure_closed _ () (real n) (model.subset_closure _ rfl)

theorem original_full_homogeneous : original.Homogeneous := by
  intro D hD f g
  let := hD.to_subtype
  obtain ⟨p,hp⟩ := original_homogeneous (realEquiv ∘ f.point) (realEquiv ∘ g.point)
    (realEquiv.injective.comp f.injective) (realEquiv.injective.comp g.injective)
  refine ⟨ofPerm p,?_⟩
  intro x
  apply realEquiv.injective
  exact hp x

/-- Generic PGO is discharged for the SAME full original group; it is not
replaced by a fresh subgroup or an assumed hidden homogeneous action. -/
theorem interpretation_PGO : interpretation.PGO := by
  intro D hD u hu
  have hi : (orbitOver model.Aut (Subtype.val '' D) u).Infinite := by
    rw [real_image] at hu ⊢
    exact real_base_orbits (realEquiv '' D) (hD.image realEquiv) u hu
  apply hi.mono
  rintro v ⟨g,hg⟩
  obtain ⟨p,hp,_⟩ := full_aut_diagonal g.val
  apply (Interpretation.mem_orbitOver_iff interpretation D u v).mpr
  refine ⟨ofPerm p,?_,?_⟩
  · intro d hd
    apply Subtype.ext
    have hf : g • d.val = d.val := g.property d.val ⟨d,hd,rfl⟩
    rw [← real_value d] at hf
    have he : real (p (realEquiv d)) = real (realEquiv d) :=
      (hp false (realEquiv d)).symm.trans hf
    exact he.trans (real_value d)
  · change lift (ofPerm p) • u = v
    rw [lift_ofPerm]
    exact (hp u.1 u.2).symm.trans hg

/-- The matching point-generated category HAS SAP, while the proved
hereditary orphan-base category does not. -/
theorem point_generated_SAP : AgeSAP original :=
  (interpretation.typed_point_generated_sap_criterion original_full_homogeneous).mpr interpretation_PGO

end CCO.PointGeneratedSAP.Examples.Matching
