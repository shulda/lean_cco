import CCO.ExactEPGeometry.OriginalRealizedAtomicSaturation
import CCO.ExactEPGeometry.OriginalCurrentExactSaturatedColour

/-!
# B062 E7 / C68–C69: actual current blocks are original saturated atoms

At any genuine prefix carrying its proved (TP), the full original-E
saturation of the complete colour of an ACTUAL current pair is exactly
the original E-saturated colour of its literal original pair projection.
This is the missing original/current atomic-block comparison, including
the real logical diagonal. No arbitrary unoccupied old atom is supplied.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- A complete tagged pair-colour saturation has witnesses in exactly
its displayed named endpoint sorts. This includes none and cross-sorts. -/
theorem setoidSaturation_taggedColour_iff
    {ι : Type u} {X : ι → Type v} (T : AtomicSource.{u,v,w} ι X)
    (S : Setoid (Sigma X)) (i j : ι) (a : Option (T.Atom i j))
    (x : X i) (y : X j) :
    setoidSaturation S (fun u v => taggedColour T u v = ⟨i,j,a⟩)
      ⟨i,x⟩ ⟨j,y⟩ ↔
      ∃ u : X i, ∃ v : X j,
        S.r ⟨i,x⟩ ⟨i,u⟩ ∧ T.colour u v = a ∧ S.r ⟨j,v⟩ ⟨j,y⟩ := by
  constructor
  · rintro ⟨⟨k,u⟩,⟨l,v⟩,hxu,hColour,hvy⟩
    have hk : k = i := congrArg Sigma.fst hColour
    have hl : l = j := congrArg (fun b : Age.Colour T => b.2.1) hColour
    subst k
    subst l
    exact ⟨u,v,hxu,by simpa only
      [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using hColour,hvy⟩
  · rintro ⟨u,v,hxu,hColour,hvy⟩
    exact ⟨⟨i,u⟩,⟨j,v⟩,hxu,
      congrArg (fun b => (⟨i,j,b⟩ : Age.Colour T)) hColour,hvy⟩

/-- E7 on the WHOLE global original-E relation, evaluated at points
in the two actual named parents of a genuinely realized current pair. -/
theorem originalCurrentAtomicSaturation_iff_original
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i j : B.Sorts} (a x : B.Point i) (b y : B.Point j) :
    originalCurrentExactSaturatedColour A B P base hOne E
      ⟨i,j,B.source.colour a b⟩ ⟨i,x⟩ ⟨j,y⟩ ↔
    originalCurrentExactSaturatedColour A A (UnaryReduct.identity A.source)
      base hOne E (taggedColour A.source (P.project ⟨i,a⟩) (P.project ⟨j,b⟩))
      (P.project ⟨i,x⟩) (P.project ⟨j,y⟩) := by
  let S := currentOriginalExactSetoid A B P base hOne E
  let T := currentOriginalExactSetoid A A (UnaryReduct.identity A.source) base hOne E
  let Ei := oldExactEqCast A.source (hOne (P.parent i)).symm E
  let Ej := oldExactEqCast A.source (hOne (P.parent j)).symm E
  have hi (u v : A.Point (P.parent i)) :
      T.r ⟨P.parent i,u⟩ ⟨P.parent i,v⟩ ↔ Ei u v :=
    originalExactGlobalRelation_same_parent A base hOne E u v
  have hj (u v : A.Point (P.parent j)) :
      T.r ⟨P.parent j,u⟩ ⟨P.parent j,v⟩ ↔ Ej u v :=
    originalExactGlobalRelation_same_parent A base hOne E u v
  change setoidSaturation S
      (fun u v => taggedColour B.source u v = ⟨i,j,B.source.colour a b⟩)
      ⟨i,x⟩ ⟨j,y⟩ ↔
    setoidSaturation T
      (fun u v => taggedColour A.source u v =
        ⟨P.parent i,P.parent j,A.source.colour (P.point i a) (P.point j b)⟩)
      ⟨P.parent i,P.point i x⟩ ⟨P.parent j,P.point j y⟩
  rw [setoidSaturation_taggedColour_iff,setoidSaturation_taggedColour_iff]
  have hL : (∃ u : B.Point i, ∃ v : B.Point j,
      S.r ⟨i,x⟩ ⟨i,u⟩ ∧ B.source.colour u v = B.source.colour a b ∧
      S.r ⟨j,v⟩ ⟨j,y⟩) ↔
      ∃ u : B.Point i, ∃ v : B.Point j,
        Ei (P.point i x) (P.point i u) ∧
        B.source.colour u v = B.source.colour a b ∧
        Ej (P.point j v) (P.point j y) := by
    apply exists_congr
    intro u
    apply exists_congr
    intro v
    exact and_congr (hi (P.point i x) (P.point i u))
      (and_congr Iff.rfl (hj (P.point j v) (P.point j y)))
  have hR : (∃ u : A.Point (P.parent i), ∃ v : A.Point (P.parent j),
      T.r ⟨P.parent i,P.point i x⟩ ⟨P.parent i,u⟩ ∧
      A.source.colour u v = A.source.colour (P.point i a) (P.point j b) ∧
      T.r ⟨P.parent j,v⟩ ⟨P.parent j,P.point j y⟩) ↔
      ∃ u : A.Point (P.parent i), ∃ v : A.Point (P.parent j),
        Ei (P.point i x) u ∧
        A.source.colour u v = A.source.colour (P.point i a) (P.point j b) ∧
        Ej v (P.point j y) := by
    apply exists_congr
    intro u
    apply exists_congr
    intro v
    exact and_congr (hi (P.point i x) u)
      (and_congr Iff.rfl (hj v (P.point j y)))
  exact hL.trans ((originalRealizedAtomicSaturation_iff
    A B P tp Ei Ej a x b y).trans hR.symm)

/-- At ANY actual certified prefix, every genuinely occurring current
atomic block on arbitrary global E-classes has exactly its two current
occupancy labels and its ORIGINAL E-saturated atom. This is source E7's
no-finer-binary-block statement, with all unary conditions retained. -/
theorem originalCurrentAtomicBlock_factorization
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i j : B.Sorts} (a : B.Point i) (b : B.Point j)
    (p q : Sigma B.Point) :
    let S := currentOriginalExactSetoid A B P base hOne E
    originalCurrentExactSaturatedColour A B P base hOne E
      ⟨i,j,B.source.colour a b⟩ p q ↔
      (∃ x : B.Point i, S.r p ⟨i,x⟩) ∧
      (∃ y : B.Point j, S.r q ⟨j,y⟩) ∧
      originalCurrentExactSaturatedColour A A (UnaryReduct.identity A.source)
        base hOne E (taggedColour A.source (P.project ⟨i,a⟩) (P.project ⟨j,b⟩))
        (P.project p) (P.project q) := by
  let S := currentOriginalExactSetoid A B P base hOne E
  let T := currentOriginalExactSetoid A A (UnaryReduct.identity A.source) base hOne E
  let D := fun u v : Sigma B.Point =>
    taggedColour B.source u v = ⟨i,j,B.source.colour a b⟩
  let Dold := fun u v : Sigma A.Point =>
    taggedColour A.source u v = taggedColour A.source (P.project ⟨i,a⟩) (P.project ⟨j,b⟩)
  have hPull (u v : Sigma B.Point) : S.r u v ↔ T.r (P.project u) (P.project v) :=
    Iff.rfl
  change setoidSaturation S D p q ↔
    (∃ x : B.Point i, S.r p ⟨i,x⟩) ∧
    (∃ y : B.Point j, S.r q ⟨j,y⟩) ∧
    setoidSaturation T Dold (P.project p) (P.project q)
  constructor
  · rintro ⟨⟨k,x⟩,⟨l,y⟩,hpx,hColour,hyq⟩
    have hk : k = i := congrArg Sigma.fst hColour
    have hl : l = j := congrArg (fun c : Age.Colour B.source => c.2.1) hColour
    subst k
    subst l
    have hFixed : setoidSaturation S D ⟨i,x⟩ ⟨j,y⟩ :=
      ⟨⟨i,x⟩,⟨j,y⟩,S.refl _,hColour,S.refl _⟩
    have hOriginal := (originalCurrentAtomicSaturation_iff_original
      A B P tp base hOne E a x b y).mp hFixed
    exact ⟨⟨x,hpx⟩,⟨y,S.symm hyq⟩,
      (setoidSaturation_congr T Dold
        ((hPull _ _).mp hpx) ((hPull _ _).mp (S.symm hyq))).mpr hOriginal⟩
  · rintro ⟨⟨x,hpx⟩,⟨y,hqy⟩,hOriginal⟩
    have hOriginalFixed := (setoidSaturation_congr T Dold
      ((hPull _ _).mp hpx) ((hPull _ _).mp hqy)).mp hOriginal
    have hFixed := (originalCurrentAtomicSaturation_iff_original
      A B P tp base hOne E a x b y).mpr hOriginalFixed
    exact (setoidSaturation_congr S D hpx hqy).mpr hFixed

end
end CCO.ExactEPGeometry
