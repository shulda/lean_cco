import CCO.RealHull.Geometry.ClassHomogeneity

/-!
# The full original invariant interval of an actual class

Restriction is inverted by literal unions of old optional colour names. The
transitivity proof moves a WHOLE relevant original class into the displayed
class. No assertion that every internal automorphism extends is used.
-/

universe u v w t
namespace CCO.RealHull.Geometry
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι)
variable (E : ColourEq S i) (a : X i)

def classRestrict (F : Set.Iic E) : ColourEq (classSource S i E a) () :=
  ⟨Setoid.comap (fun x : ClassPoint S i E a => x.val) F.val.val, by
    intro x y x' y' hc
    exact F.val.property x.val y.val x'.val y'.val
      ((inducedColour_eq_iff S i _ x y x' y').mp hc)⟩

def classExtendRel (V : ColourEq (classSource S i E a) ()) (x y : X i) : Prop :=
  E x y ∧ ∃ p q : ClassPoint S i E a,
    S.colour x y = S.colour p.val q.val ∧ V p q

theorem classExtendRel_colour (V : ColourEq (classSource S i E a) ())
    (x y x' y' : X i) (hc : S.colour x y = S.colour x' y') :
    classExtendRel S i E a V x y ↔ classExtendRel S i E a V x' y' := by
  constructor
  · rintro ⟨he,p,q,hpq,hv⟩
    exact ⟨(E.property x y x' y' hc).mp he,p,q,hc.symm.trans hpq,hv⟩
  · rintro ⟨he,p,q,hpq,hv⟩
    exact ⟨(E.property x y x' y' hc).mpr he,p,q,hc.trans hpq,hv⟩

theorem classExtendRel_on_class (V : ColourEq (classSource S i E a) ())
    (p q : ClassPoint S i E a) :
    classExtendRel S i E a V p.val q.val ↔ V p q := by
  constructor
  · rintro ⟨_,r,s,hc,hv⟩
    exact (V.property p q r s ((inducedColour_eq_iff S i _ p q r s).mpr hc)).mpr hv
  · intro hv
    exact ⟨E.val.trans (E.val.symm p.property) q.property,p,q,rfl,hv⟩

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)
include H

theorem classExtendRel_trans (V : ColourEq (classSource S i E a) ())
    (x y z : X i) (hxy : classExtendRel S i E a V x y)
    (hyz : classExtendRel S i E a V y z) : classExtendRel S i E a V x z := by
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x a
  have hy : E a (g • y) := by
    simpa only [hg] using (class_group_invariant S i H E g x y).mpr hxy.1
  have hz : E a (g • z) := by
    simpa only [hg] using
      (class_group_invariant S i H E g x z).mpr (E.val.trans hxy.1 hyz.1)
  let p : ClassPoint S i E a := ⟨a,E.val.refl a⟩
  let q : ClassPoint S i E a := ⟨g • y,hy⟩
  let r : ClassPoint S i E a := ⟨g • z,hz⟩
  have hpq : S.colour x y = S.colour p.val q.val := by
    simpa only [p,q,hg] using (S.colourInvariant_of_homogeneous H g x y).symm
  have hqr : S.colour y z = S.colour q.val r.val :=
    (S.colourInvariant_of_homogeneous H g y z).symm
  have hpr : S.colour x z = S.colour p.val r.val := by
    simpa only [p,r,hg] using (S.colourInvariant_of_homogeneous H g x z).symm
  have hvpq := (classExtendRel_on_class S i E a V p q).mp
    ((classExtendRel_colour S i E a V x y p.val q.val hpq).mp hxy)
  have hvqr := (classExtendRel_on_class S i E a V q r).mp
    ((classExtendRel_colour S i E a V y z q.val r.val hqr).mp hyz)
  exact (classExtendRel_colour S i E a V x z p.val r.val hpr).mpr
    ((classExtendRel_on_class S i E a V p r).mpr (V.val.trans hvpq hvqr))

def classExtend (V : ColourEq (classSource S i E a) ()) : ColourEq S i :=
  ⟨{
    r := classExtendRel S i E a V
    iseqv := {
      refl := by
        intro x
        refine ⟨E.val.refl x,⟨a,E.val.refl a⟩,⟨a,E.val.refl a⟩,?_,V.val.refl _⟩
        exact ((S.colour_none_iff x x).mpr rfl).trans
          ((S.colour_none_iff a a).mpr rfl).symm
      symm := by
        rintro x y ⟨he,p,q,hc,hv⟩
        refine ⟨E.val.symm he,q,p,?_,V.val.symm hv⟩
        rw [S.colour_reverse x y,S.colour_reverse p.val q.val,hc]
      trans := fun hxy hyz => classExtendRel_trans S i E a H V _ _ _ hxy hyz
    }
  },classExtendRel_colour S i E a V⟩

theorem classExtend_le (V : ColourEq (classSource S i E a) ()) :
    classExtend S i E a H V ≤ E := fun _ _ h => h.1

theorem class_restrict_extend (V : ColourEq (classSource S i E a) ()) :
    classRestrict S i E a ⟨classExtend S i E a H V,classExtend_le S i E a H V⟩ = V := by
  apply ColourEq.ext
  exact classExtendRel_on_class S i E a V

theorem class_extend_restrict (F : Set.Iic E) :
    classExtend S i E a H (classRestrict S i E a F) = F.val := by
  apply ColourEq.ext
  intro x y
  constructor
  · rintro ⟨_,p,q,hc,hv⟩
    exact (F.val.property x y p.val q.val hc).mpr hv
  · intro hxy
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x a
    have hy : E a (g • y) := by
      simpa only [hg] using (class_group_invariant S i H E g x y).mpr (F.property hxy)
    let p : ClassPoint S i E a := ⟨a,E.val.refl a⟩
    let q : ClassPoint S i E a := ⟨g • y,hy⟩
    have hc : S.colour x y = S.colour p.val q.val := by
      simpa only [p,q,hg] using (S.colourInvariant_of_homogeneous H g x y).symm
    exact ⟨F.property hxy,p,q,hc,(F.val.property x y p.val q.val hc).mp hxy⟩

theorem classExtend_mono {V W : ColourEq (classSource S i E a) ()} (hVW : V ≤ W) :
    classExtend S i E a H V ≤ classExtend S i E a H W := by
  rintro x y ⟨he,p,q,hc,hv⟩
  exact ⟨he,p,q,hc,hVW hv⟩

noncomputable def classIntervalIso : Set.Iic E ≃o ColourEq (classSource S i E a) () where
  toFun := classRestrict S i E a
  invFun V := ⟨classExtend S i E a H V,classExtend_le S i E a H V⟩
  left_inv F := Subtype.ext (class_extend_restrict S i E a H F)
  right_inv := class_restrict_extend S i E a H
  map_rel_iff' := by
    intro F K
    constructor
    · intro h
      have hh := classExtend_mono S i E a H h
      change classExtend S i E a H (classRestrict S i E a F) ≤
        classExtend S i E a H (classRestrict S i E a K) at hh
      rw [class_extend_restrict,class_extend_restrict] at hh
      exact hh
    · intro h x y hxy
      exact h hxy

end CCO.RealHull.Geometry
