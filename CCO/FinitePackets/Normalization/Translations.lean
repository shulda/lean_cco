import CCO.FinitePackets.Normalization.ThinBasic
import Mathlib.Algebra.Group.Subgroup.Basic

/-! The actual group of equivariant permutations with displacement in F.
It is built before its members are known to preserve all source colours.
Thinness identifies its members with the actual equality-inclusive F-atoms.
No packet origins or quotient-action sections enter the construction. -/
universe v w t
namespace CCO.FinitePackets.Normalization
open CCO.RealHull.Geometry CCO.ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (F : ColourEq S ()) (G : Type t) [Group G] [MulAction G M]

def translationSubgroup : Subgroup (Equiv.Perm M) where
  carrier := {e | (∀ (g : G) (x : M), e (g • x) = g • e x) ∧ ∀ x : M, F x (e x)}
  one_mem' := ⟨fun _ _ => rfl,fun x => F.val.refl x⟩
  mul_mem' := by
    intro e f he hf
    refine ⟨?_,?_⟩
    · intro g x
      change e (f (g • x)) = g • e (f x)
      rw [hf.1,he.1]
    · intro x
      exact F.val.trans (hf.2 x) (he.2 (f x))
  inv_mem' := by
    intro e he
    refine ⟨?_,?_⟩
    · intro g x
      apply e.injective
      change e (e.symm (g • x)) = e (g • e.symm x)
      rw [Equiv.apply_symm_apply,he.1,Equiv.apply_symm_apply]
    · intro x
      have hh := he.2 (e.symm x)
      rw [Equiv.apply_symm_apply] at hh
      exact F.val.symm hh

abbrev Translation := ↥(translationSubgroup S F G)

theorem translation_equivariant (e : Translation S F G) (g : G) (x : M) :
    e.val (g • x) = g • e.val x := e.property.1 g x

theorem translation_in_packet (e : Translation S F G) (x : M) :
    F x (e.val x) := e.property.2 x

variable {G} (H : HomogeneousSource S G)
include H

theorem translation_colour_constant (e : Translation S F G) (x y : M) :
    col S x (e.val x) = col S y (e.val y) := by
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H () x y
  rw [← hg,translation_equivariant S F G e g x]
  exact (col_invariant S H g x (e.val x)).symm

noncomputable def translationColour (e : Translation S F G) : FullColour S :=
  let x := Classical.choice (S.nonemptySort ())
  col S x (e.val x)

theorem translationColour_at (e : Translation S F G) (x : M) :
    col S x (e.val x) = translationColour S F (G := G) e :=
  translation_colour_constant S F H e x _

theorem translationColour_below (e : Translation S F G) :
    FullColourBelow S F (translationColour S F (G := G) e) := by
  let x := Classical.choice (S.nonemptySort ())
  exact fullColourBelow_at S F x (e.val x) (translation_in_packet S F G e x)

variable (hthin : ThinBottom S F)
include hthin

noncomputable def colourTranslation (c : FullColour S) (hc : FullColourBelow S F c) :
    Translation S F G :=
  ⟨thinPerm S c (hthin c hc),
    ⟨thinPerm_equivariant S H c (hthin c hc),
      fun x => hc x _ (thinPerm_colour S c (hthin c hc) x)⟩⟩

theorem colourTranslation_apply (c : FullColour S) (hc : FullColourBelow S F c) (x : M) :
    col S x ((colourTranslation S F H hthin c hc).val x) = c :=
  thinPerm_colour S c (hthin c hc) x

theorem translationColour_injective : Function.Injective (translationColour S F (G := G)) := by
  intro e f hef
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have hc := hthin _ (translationColour_below S F H e)
  exact ((hc x).unique (translationColour_at S F H e x)
    ((translationColour_at S F H f x).trans hef.symm))

noncomputable def translationColourEquiv :
    Translation S F G ≃ {c : FullColour S // FullColourBelow S F c} where
  toFun e := ⟨translationColour S F (G := G) e,translationColour_below S F H e⟩
  invFun c := colourTranslation S F H hthin c.val c.property
  left_inv e := by
    apply translationColour_injective S F H hthin
    let x := Classical.choice (S.nonemptySort ())
    exact (translationColour_at S F H _ x).symm.trans
      (colourTranslation_apply S F H hthin _ _ x)
  right_inv c := by
    apply Subtype.ext
    let x := Classical.choice (S.nonemptySort ())
    exact (translationColour_at S F H _ x).symm.trans
      (colourTranslation_apply S F H hthin c.val c.property x)

theorem translation_finite : Finite (Translation S F G) := by
  letI := S.finiteAtom () ()
  exact Finite.of_injective _ (translationColour_injective S F H hthin)

theorem translation_square (e : Translation S F G) : e * e = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change e.val (e.val x) = x
  have hc := hthin _ (translationColour_below S F H e)
  apply (hc (e.val x)).unique
  · exact translationColour_at S F H e (e.val x)
  · exact (col_symm S (e.val x) x).trans (translationColour_at S F H e x)

theorem translation_inv (e : Translation S F G) : e⁻¹ = e := by
  calc
    e⁻¹ = e⁻¹ * (e * e) := by rw [translation_square S F H hthin,mul_one]
    _ = e := by rw [← mul_assoc,inv_mul_cancel,one_mul]

theorem translation_comm (e f : Translation S F G) : e * f = f * e := by
  calc
    e * f = (e * f)⁻¹ := (translation_inv S F H hthin _).symm
    _ = f⁻¹ * e⁻¹ := mul_inv_rev _ _
    _ = f * e := by rw [translation_inv S F H hthin,translation_inv S F H hthin]

def translationCommGroup : CommGroup (Translation S F G) :=
  { __ := (inferInstance : Group (Translation S F G))
    mul_comm := translation_comm S F H hthin }

noncomputable def packetTranslationEquiv (x : M) :
    Translation S F G ≃ {y : M // F x y} :=
  Equiv.ofBijective (fun e => ⟨e.val x,translation_in_packet S F G e x⟩) (by
    constructor
    · intro e f hef
      apply translationColour_injective S F H hthin
      have hv := congrArg Subtype.val hef
      exact (translationColour_at S F H e x).symm.trans
        ((congrArg (col S x) hv).trans (translationColour_at S F H f x))
    · intro y
      let hc := fullColourBelow_at S F x y.val y.property
      refine ⟨colourTranslation S F H hthin (col S x y.val) hc,?_⟩
      apply Subtype.ext
      exact thinNeighbour_eq S _ (hthin _ hc) rfl)

theorem translation_regular (x y : M) (hxy : F x y) :
    ∃! e : Translation S F G, e.val x = y := by
  let p := packetTranslationEquiv S F H hthin x
  refine ⟨p.symm ⟨y,hxy⟩,?_,?_⟩
  · exact congrArg Subtype.val (p.apply_symm_apply ⟨y,hxy⟩)
  · intro e he
    apply p.injective
    apply Subtype.ext
    exact he.trans (congrArg Subtype.val (p.apply_symm_apply ⟨y,hxy⟩)).symm

end CCO.FinitePackets.Normalization
