import CCO.RealHull.Geometry.ClassIntervals
import CCO.ParityHasse.Original.RelativeIndices

/-! The interval target is the FULL actual class automorphism invariant lattice,
not merely invariance under selected ambient motions. Relative classes and all
chain indices are carried by literal old-point bijections. -/
universe u v w t
namespace CCO.RealHull.Geometry
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι)

def InducedFullEq (Z : Set (X i)) :=
  {F : Setoid Z // ∀ (g : inducedAut S i Z) x y, F (g.val x) (g.val y) ↔ F x y}

instance inducedFullEqPartialOrder (Z : Set (X i)) : PartialOrder (InducedFullEq S i Z) :=
  inferInstanceAs (PartialOrder {F : Setoid Z //
    ∀ (g : inducedAut S i Z) x y, F (g.val x) (g.val y) ↔ F x y})

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G) (E : ColourEq S i) (a : X i)

noncomputable def classColourFullIso :
    ColourEq (classSource S i E a) () ≃o InducedFullEq S i {x | E a x} where
  toFun F := ⟨F.val,fun g x y => F.property _ _ _ _ (g.property x y)⟩
  invFun F := ⟨F.val,by
    intro x y x' y' hc
    obtain ⟨g,hgx,hgy⟩ := (classSource S i E a).pair_homogeneous_of_homogeneous
      (class_homogeneous S i H E a) x x' y y' hc
    have hh := F.property g x y
    change F.val (g.val x) (g.val y) ↔ F.val x y at hh
    change g.val x = x' at hgx
    change g.val y = y' at hgy
    rw [hgx,hgy] at hh
    exact hh.symm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

noncomputable def classFullIntervalIso :
    Set.Iic E ≃o InducedFullEq S i {x | E a x} :=
  (classIntervalIso S i E a H).trans (classColourFullIso S i H E a)

def classRelativeEquiv (F K : Set.Iic E) (p : ClassPoint S i E a) :
    RelativeClass F.val.val K.val.val p.val ≃
      RelativeClass (classRestrict S i E a F).val (classRestrict S i E a K).val p where
  toFun := Quotient.map (fun x =>
    (⟨(⟨x.val,E.val.trans p.property (K.property x.property)⟩ : ClassPoint S i E a),x.property⟩ :
      {x : ClassPoint S i E a // (classRestrict S i E a K) p x})) (fun _ _ h => h)
  invFun := Quotient.map (fun x => (⟨x.val.val,x.property⟩ : {x // K.val p.val x}))
    (fun _ _ h => h)
  left_inv q := by
    induction q using Quotient.inductionOn with | _ x => rfl
  right_inv q := by
    induction q using Quotient.inductionOn with | _ x => rfl

theorem class_relativeIndex (F K : Set.Iic E) (p : ClassPoint S i E a) :
    relativeIndex F.val.val K.val.val p.val =
      relativeIndex (classRestrict S i E a F).val (classRestrict S i E a K).val p :=
  Nat.card_congr (classRelativeEquiv S i E a F K p)

end CCO.RealHull.Geometry
