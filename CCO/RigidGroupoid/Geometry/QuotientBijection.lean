import CCO.RigidGroupoid.Geometry.Bridge
import CCO.RawExact.CanonicalQuotients
import CCO.RawExact.Saturation

/-! Actual quotient-class bijections and their free action. A real bridge may
have many real successors. Its map is defined only on the actual kernel
classes, with equivariance for the ORIGINAL ambient action proved. -/

universe u v w t
namespace CCO.RigidGroupoid.Geometry
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)

include H

namespace Kernel
variable {S} {i : ι} (A : Kernel S i)
abbrev Class := Quotient A.setoid
def project : X i → A.Class := Quotient.mk A.setoid

@[instance_reducible] def action : MulAction G A.Class := by
  letI : RawExact.CanonicalQuotients.Invariant G A.setoid := ⟨A.exact.invariant S H⟩
  exact RawExact.CanonicalQuotients.quotientMulAction A.setoid

theorem project_equivariant (g : G) (x : X i) :
    letI := A.action H
    A.project (g • x) = g • A.project x := rfl

theorem class_transitive (q r : A.Class) :
    letI := A.action H
    ∃ g : G, g • q = r := by
  letI := A.action H
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x y
      exact ⟨g,congrArg A.project hg⟩
end Kernel

namespace Arrow
variable {S} {i j : ι} {A : Kernel S i} {B : Kernel S j} (R : Arrow S A B)

noncomputable def pointImage (x : X i) : X j := Classical.choose (R.exact.serial S H x)

theorem pointImage_spec (x : X i) : R.rel x (R.pointImage H x) :=
  Classical.choose_spec (R.exact.serial S H x)

theorem pointImage_respects {x x' : X i} (hx : A.rel x x') :
    B.rel (R.pointImage H x) (R.pointImage H x') := by
  rw [← R.target]
  refine ⟨x,R.pointImage_spec H x,?_⟩
  rw [← R.left]
  exact ⟨x',hx,R.pointImage_spec H x'⟩

noncomputable def quotientMap : A.Class → B.Class :=
  Quotient.lift (fun x => B.project (R.pointImage H x))
    (fun _ _ h => Quotient.sound (R.pointImage_respects H h))

theorem quotientMap_project (x : X i) :
    R.quotientMap H (A.project x) = B.project (R.pointImage H x) := rfl

theorem quotientMap_eq_iff (x : X i) (y : X j) :
    R.quotientMap H (A.project x) = B.project y ↔ R.rel x y := by
  constructor
  · intro h
    have hb : B.rel (R.pointImage H x) y := Quotient.exact h
    rw [← R.right]
    exact ⟨R.pointImage H x,R.pointImage_spec H x,hb⟩
  · intro hxy
    apply Quotient.sound
    change B.rel (R.pointImage H x) y
    rw [← R.target]
    exact ⟨x,R.pointImage_spec H x,hxy⟩

theorem inverse_quotientMap (q : A.Class) :
    R.inv.quotientMap H (R.quotientMap H q) = q := by
  induction q using Quotient.inductionOn with
  | _ x =>
    exact (R.inv.quotientMap_eq_iff H (R.pointImage H x) x).mpr (R.pointImage_spec H x)

noncomputable def quotientEquiv : A.Class ≃ B.Class where
  toFun := R.quotientMap H
  invFun := R.inv.quotientMap H
  left_inv := R.inverse_quotientMap H
  right_inv := R.inv.inverse_quotientMap H

theorem quotientMap_equivariant (g : G) (q : A.Class) :
    letI := A.action H
    letI := B.action H
    R.quotientMap H (g • q) = g • R.quotientMap H q := by
  letI := A.action H
  letI := B.action H
  induction q using Quotient.inductionOn with
  | _ x =>
    change R.quotientMap H (A.project (g • x)) = B.project (g • R.pointImage H x)
    exact (R.quotientMap_eq_iff H _ _).mpr
      (R.exact.invariant S H g x _ (R.pointImage_spec H x))

/-- Faithful readout: the full pullback of the actual quotient bijection graph
is exactly the original rectangular bridge relation. -/
theorem graph_pullback :
    GroupActions.pullback A.project B.project (fun q r => R.quotientMap H q = r) = R.rel := by
  funext x y
  exact propext (R.quotientMap_eq_iff H x y)

theorem quotient_graph_orbital {x : X i} {y : X j} (hxy : R.rel x y) :
    letI := A.action H
    letI := B.action H
    (fun q r => R.quotientMap H q = r) =
      GroupActions.orbital (G := G) (A.project x) (B.project y) := by
  letI := A.action H
  letI := B.action H
  funext q r
  apply propext
  constructor
  · intro hqr
    obtain ⟨g,hg⟩ := A.class_transitive H (A.project x) q
    refine ⟨g,hg,?_⟩
    have he := R.quotientMap_equivariant H g (A.project x)
    rw [hg,(R.quotientMap_eq_iff H x y).mpr hxy,hqr] at he
    exact he.symm
  · rintro ⟨g,hg,hr⟩
    have he := R.quotientMap_equivariant H g (A.project x)
    rwa [hg,(R.quotientMap_eq_iff H x y).mpr hxy,hr] at he

/-- C15: ANY actual old atom in the bridge, logical equality included,
gives its one-atom rectangular presentation. -/
theorem rectangular {x : X i} {y : X j} (hxy : R.rel x y) :
    R.rel = RawExact.saturate A.rel (S.rawAtomRel (S.colour x y)) B.rel := by
  letI := A.action H
  letI := B.action H
  calc
    R.rel = GroupActions.pullback A.project B.project
        (fun q r => R.quotientMap H q = r) := (R.graph_pullback H).symm
    _ = GroupActions.pullback A.project B.project
        (GroupActions.orbital (G := G) (A.project x) (B.project y)) := by
      rw [R.quotient_graph_orbital H hxy]
    _ = RawExact.saturate (GroupActions.kernel A.project)
        (GroupActions.orbital (G := G) x y) (GroupActions.kernel B.project) :=
      RawExact.equivariant_orbit_pullback A.project B.project
        (A.project_equivariant H) (B.project_equivariant H) x y
    _ = RawExact.saturate A.rel (S.rawAtomRel (S.colour x y)) B.rel := by
      have hA : GroupActions.kernel A.project = A.rel := by
        funext a b
        exact propext ⟨Quotient.exact,Quotient.sound⟩
      have hB : GroupActions.kernel B.project = B.rel := by
        funext a b
        exact propext ⟨Quotient.exact,Quotient.sound⟩
      rw [hA,hB,RawExact.actual_pair_orbital_of_homogeneous S H x y]

theorem eq_of_agree_at (T : Arrow S A B) (q : A.Class)
    (h : R.quotientMap H q = T.quotientMap H q) : R = T := by
  have hall (r : A.Class) : R.quotientMap H r = T.quotientMap H r := by
    letI := A.action H
    letI := B.action H
    obtain ⟨g,rfl⟩ := A.class_transitive H q r
    rw [R.quotientMap_equivariant H,T.quotientMap_equivariant H,h]
  apply Arrow.ext
  funext x y
  apply propext
  rw [← R.quotientMap_eq_iff H,← T.quotientMap_eq_iff H,hall]

theorem eq_of_common_real_pair (T : Arrow S A B) {x : X i} {y : X j}
    (hR : R.rel x y) (hT : T.rel x y) : R = T :=
  R.eq_of_agree_at H T (A.project x)
    (((R.quotientMap_eq_iff H x y).mpr hR).trans ((T.quotientMap_eq_iff H x y).mpr hT).symm)

end Arrow
end CCO.RigidGroupoid.Geometry
