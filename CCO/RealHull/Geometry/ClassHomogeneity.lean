import CCO.RealHull.Geometry.ClassSource

/-! Actual ambient motions supply finite homogeneity of one equivalence class.
The resulting group is the FULL induced-language automorphism group. -/

universe u v w t
namespace CCO.RealHull.Geometry
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι)

theorem induced_homogeneous_of_extension (Z : Set (X i)) [Nonempty Z]
    (extend : ∀ {V : Type v} [Finite V] (f h : V → Z),
      (∀ x y, S.colour (f x).val (f y).val = S.colour (h x).val (h y).val) →
      ∃ g : inducedAut S i Z, ∀ v, g • f v = h v) :
    HomogeneousSource (inducedSource S i Z) (inducedAut S i Z) where
  preserves_sort := by intro g p; cases p with | mk j x => cases j; rfl
  preserves_colours := by
    intro g p q
    cases p with | mk j x => cases q with | mk k y =>
      cases j; cases k
      exact congrArg (fun c => (⟨(),(),c⟩ : Σ j : Unit, Σ k : Unit,
        Option ((inducedSource S i Z).Atom j k))) (g.property x y)
  extends_finite_diagram := by
    intro V hV f h hc
    have hcol : ∀ x y, S.colour (f x).2.val (f y).2.val =
        S.colour (h x).2.val (h y).2.val := by
      intro x y
      apply (inducedColour_eq_iff S i Z _ _ _ _).mp
      have hh := hc x y
      cases hf : f x with | mk j a => cases hk : f y with | mk k b =>
        cases hm : h x with | mk l c => cases hn : h y with | mk m d =>
          cases j; cases k; cases l; cases m
          simpa only [hf,hk,hm,hn,taggedColour,inducedSource,Sigma.mk.injEq,heq_eq_eq,true_and] using hh
    obtain ⟨g,hg⟩ := extend (fun x => (f x).2) (fun x => (h x).2) hcol
    refine ⟨g,fun x => ?_⟩
    cases hf : f x with | mk j a => cases hh : h x with | mk k b =>
      cases j; cases k
      have hv := hg x
      rw [hf,hh] at hv
      exact congrArg (Sigma.mk ()) hv

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)
include H

theorem class_group_invariant (E : ColourEq S i) (g : G) (x y : X i) :
    E (g • x) (g • y) ↔ E x y :=
  E.property _ _ _ _ (S.colourInvariant_of_homogeneous H g x y)

theorem class_motion_membership (E : ColourEq S i) (a : X i) (g : G)
    (hg : E a (g • a)) (x : X i) : E a (g • x) ↔ E a x := by
  constructor
  · intro hx
    exact (class_group_invariant S i H E g a x).mp (E.val.trans (E.val.symm hg) hx)
  · intro hx
    exact E.val.trans hg ((class_group_invariant S i H E g a x).mpr hx)

def classPerm (E : ColourEq S i) (a : X i) (g : G) (hg : E a (g • a)) :
    Equiv.Perm (ClassPoint S i E a) where
  toFun x := ⟨g • x.val,(class_motion_membership S i H E a g hg x.val).mpr x.property⟩
  invFun y := ⟨g⁻¹ • y.val,by
    apply (class_motion_membership S i H E a g hg (g⁻¹ • y.val)).mp
    simpa only [smul_inv_smul] using y.property⟩
  left_inv x := Subtype.ext (inv_smul_smul g x.val)
  right_inv x := Subtype.ext (smul_inv_smul g x.val)

def classAutMotion (E : ColourEq S i) (a : X i) (g : G) (hg : E a (g • a)) :
    inducedAut S i {x | E a x} :=
  ⟨classPerm S i H E a g hg, fun x y =>
    (inducedColour_eq_iff S i _ _ _ _ _).mpr (S.colourInvariant_of_homogeneous H g x.val y.val)⟩

theorem class_finite_extension (E : ColourEq S i) (a : X i)
    {V : Type v} [Finite V] (f h : V → ClassPoint S i E a)
    (hc : ∀ x y, S.colour (f x).val (f y).val = S.colour (h x).val (h y).val) :
    ∃ g : inducedAut S i {x | E a x}, ∀ v, g.val (f v) = h v := by
  classical
  by_cases hv : Nonempty V
  · let f' : ULift.{u} V → Sigma X := fun x => ⟨i,(f x.down).val⟩
    let h' : ULift.{u} V → Sigma X := fun x => ⟨i,(h x.down).val⟩
    have hcol : ∀ x y, taggedColour S (f' x) (f' y) = taggedColour S (h' x) (h' y) := by
      intro x y
      exact congrArg (fun c => (⟨i,i,c⟩ : Σ j, Σ k, Option (S.Atom j k))) (hc x.down y.down)
    obtain ⟨g,hg⟩ := H.extends_finite_diagram f' h' hcol
    have hgv (x : V) : g • (f x).val = (h x).val := by
      have hh := hg (ULift.up x)
      simpa only [f',h',Sigma.smul_mk,Sigma.mk.injEq,heq_eq_eq,true_and] using hh
    obtain ⟨x⟩ := hv
    have hga : E a (g • a) := by
      have he := (class_group_invariant S i H E g a (f x).val).mpr (f x).property
      rw [hgv x] at he
      exact E.val.trans (h x).property (E.val.symm he)
    refine ⟨classAutMotion S i H E a g hga, fun x => ?_⟩
    apply Subtype.ext
    exact hgv x
  · exact ⟨1,fun x => False.elim (hv ⟨x⟩)⟩

theorem class_homogeneous (E : ColourEq S i) (a : X i) :
    HomogeneousSource (classSource S i E a) (inducedAut S i {x | E a x}) := by
  letI : Nonempty {x | E a x} := ⟨⟨a,E.val.refl a⟩⟩
  exact induced_homogeneous_of_extension S i _ (class_finite_extension S i H E a)

theorem class_atom_occurs_iff (E : ColourEq S i) (a : X i) (c : S.Atom i i) :
    (∃ x y : ClassPoint S i E a, S.colour x.val y.val = some c) ↔
      ∀ x y : X i, S.colour x y = some c → E x y := by
  constructor
  · rintro ⟨x,y,hxy⟩ u v huv
    exact (E.property x.val y.val u v (hxy.trans huv.symm)).mp
      (E.val.trans (E.val.symm x.property) y.property)
  · intro hc
    obtain ⟨x,y,hxy⟩ := S.realized c
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x a
    have hy : E a (g • y) := by
      have hh := (class_group_invariant S i H E g x y).mpr (hc x y hxy)
      simpa only [hg] using hh
    refine ⟨⟨a,E.val.refl a⟩,⟨g • y,hy⟩,?_⟩
    have hh := S.colourInvariant_of_homogeneous H g x y
    rw [hg,hxy] at hh
    exact hh

end CCO.RealHull.Geometry
