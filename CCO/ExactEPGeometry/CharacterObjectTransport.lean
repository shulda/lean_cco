import CCO.RigidGroupoid.Phase.AbstractCharacter
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Exact character transport across a genuine object bijection

Use the literal inverse object bijection and only equality arrows. In
particular no arbitrary connecting-arrow choices change the character by
an object coboundary. The full Hom inverse and all functor laws are actual
data; the source consumer constructs them from equal genuine gate kernels.
-/

universe u₁ u₂ v₁ v₂
namespace CCO.ExactEPGeometry
open CategoryTheory
open RigidGroupoid.Phase

noncomputable section

variable {J : Type u₁} {K : Type u₂}
variable [Category.{v₁} J] [Category.{v₂} K]

/-- Pull back a whole character along a genuine functor. -/
def characterFunctorPullback (F : J ⥤ K) (χ : Abstract.Character K) :
    Abstract.Character J where
  value R := χ.value (F.map R)
  map_id a := by rw [F.map_id]; exact χ.map_id _
  map_comp R T := by rw [F.map_comp]; exact χ.map_comp _ _

/-- A bijective-on-objects full faithful functor has a strict object inverse.
The only coherence arrows used are those induced by literal equalities. -/
def strictObjectInverse (F : J ⥤ K) (FF : F.FullyFaithful)
    (e : J ≃ K) (he : ∀ a, F.obj a = e a) : K ⥤ J where
  obj b := e.symm b
  map {a b} R := FF.preimage
    (eqToHom ((he _).trans (e.apply_symm_apply a)) ≫ R ≫
      eqToHom ((he _).trans (e.apply_symm_apply b)).symm)
  map_id a := by simp
  map_comp R T := by
    apply FF.map_injective
    simp [Category.assoc]

/-- Equality arrows always have character zero. -/
theorem character_eqToHom (χ : Abstract.Character J) {a b : J} (h : a = b) :
    χ.value (eqToHom h) = 0 := by
  subst b
  exact χ.map_id a

/-- Full faithful preimages preserve literal equality arrows. -/
theorem fullyFaithful_preimage_eqToHom (F : J ⥤ K) (FF : F.FullyFaithful)
    {a b : J} (h : a = b) :
    FF.preimage (eqToHom (congrArg F.obj h)) = eqToHom h := by
  apply FF.map_injective
  subst b
  simp

/-- The strict inverse preserves the exact supplied character on EVERY
forward Hom, without any additional gauge correction. -/
theorem characterStrictTransport_map (F : J ⥤ K) (FF : F.FullyFaithful)
    (e : J ≃ K) (he : ∀ a, F.obj a = e a) (χ : Abstract.Character J)
    {a b : J} (R : a ⟶ b) :
    (characterFunctorPullback (strictObjectInverse F FF e he) χ).value
      (F.map R) = χ.value R := by
  let ha : e.symm (F.obj a) = a :=
    (congrArg e.symm (he a)).trans (e.symm_apply_apply a)
  let hb : e.symm (F.obj b) = b :=
    (congrArg e.symm (he b)).trans (e.symm_apply_apply b)
  have hha : (he (e.symm (F.obj a))).trans (e.apply_symm_apply (F.obj a)) =
      congrArg F.obj ha := Subsingleton.elim _ _
  have hhb : ((he (e.symm (F.obj b))).trans (e.apply_symm_apply (F.obj b))).symm =
      congrArg F.obj hb.symm := Subsingleton.elim _ _
  change χ.value (FF.preimage
    (eqToHom ((he _).trans (e.apply_symm_apply (F.obj a))) ≫ F.map R ≫
      eqToHom ((he _).trans (e.apply_symm_apply (F.obj b))).symm)) = _
  rw [hha,hhb,FF.preimage_comp,FF.preimage_comp,
    fullyFaithful_preimage_eqToHom F FF ha,
    fullyFaithful_preimage_eqToHom F FF hb.symm,
    FF.preimage_map,χ.map_comp,χ.map_comp,character_eqToHom,
    character_eqToHom,zero_add,add_zero]

end
end CCO.ExactEPGeometry
