import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.End

/-! Full owner support recovers a semilinear component ONTO THE IMAGE of
the given group. This does not identify it with the full automorphism group,
choose a section, or infer fine-owner support from a coarser trim image. -/
universe u v w
namespace CCO.FullRows.Semilinear
variable {U : Type u} {V : Type v} (Gamma : Subgroup (Equiv.Perm U))

/-- The actual group of ALL semilinear pairs preserving literal colours. -/
def pairGroup {Atom : Type w} (own : V → U) (colour : V → V → Atom) :
    Subgroup (Gamma × Equiv.Perm V) where
  carrier := {a | (∀ x, own (a.2 x) = (a.1 : Equiv.Perm U) (own x)) ∧
    ∀ x y, colour (a.2 x) (a.2 y) = colour x y}
  one_mem' := ⟨by intro x; rfl,by intro x y; rfl⟩
  mul_mem' := by
    intro a b ha hb
    constructor
    · intro x
      change own (a.2 (b.2 x)) = (a.1 : Equiv.Perm U) ((b.1 : Equiv.Perm U) (own x))
      rw [ha.1,hb.1]
    · intro x y
      change colour (a.2 (b.2 x)) (a.2 (b.2 y)) = _
      rw [ha.2,hb.2]
  inv_mem' := by
    intro a ha
    constructor
    · intro x
      change own (a.2.symm x) = (a.1 : Equiv.Perm U).symm (own x)
      have hh := ha.1 (a.2.symm x)
      change own (a.2 (a.2.symm x)) = (a.1 : Equiv.Perm U) (own (a.2.symm x)) at hh
      have hh' := congrArg (a.1 : Equiv.Perm U).symm hh.symm
      simpa only [Equiv.apply_symm_apply,Equiv.symm_apply_apply] using hh'
    · intro x y
      change colour (a.2.symm x) (a.2.symm y) = colour x y
      simpa only [Equiv.apply_symm_apply] using (ha.2 (a.2.symm x) (a.2.symm y)).symm

theorem pairGroup_owner {Atom : Type w} (own : V → U) (colour : V → V → Atom)
    (a : pairGroup Gamma own colour) (x : V) :
    own (a.val.2 x) = (a.val.1 : Equiv.Perm U) (own x) := a.property.1 x

theorem pairGroup_colour {Atom : Type w} (own : V → U) (colour : V → V → Atom)
    (a : pairGroup Gamma own colour) (x y : V) :
    colour (a.val.2 x) (a.val.2 y) = colour x y := a.property.2 x y

def forget (L : Subgroup (Gamma × Equiv.Perm V)) : L →* Equiv.Perm V :=
  (MonoidHom.snd Gamma (Equiv.Perm V)).comp L.subtype

def language (L : Subgroup (Gamma × Equiv.Perm V)) : L →* Gamma :=
  (MonoidHom.fst Gamma (Equiv.Perm V)).comp L.subtype

variable {Gamma}

theorem forget_injective (own : V → U) (hsupport : Function.Surjective own)
    (L : Subgroup (Gamma × Equiv.Perm V))
    (hown : ∀ (a : L) x, own (a.val.2 x) = (a.val.1 : Equiv.Perm U) (own x)) :
    Function.Injective (forget Gamma L) := by
  intro a b hab
  change a.val.2 = b.val.2 at hab
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Equiv.ext
    intro u
    obtain ⟨x,rfl⟩ := hsupport u
    calc
      _ = own (a.val.2 x) := (hown a x).symm
      _ = own (b.val.2 x) := congrArg (fun f : Equiv.Perm V => own (f x)) hab
      _ = _ := hown b x
  · exact hab

noncomputable def forgetIso (own : V → U) (hsupport : Function.Surjective own)
    (L : Subgroup (Gamma × Equiv.Perm V))
    (hown : ∀ (a : L) x, own (a.val.2 x) = (a.val.1 : Equiv.Perm U) (own x)) :
    L ≃* (forget Gamma L).range :=
  MonoidHom.ofInjective (forget_injective own hsupport L hown)

noncomputable def languageOnImage (own : V → U) (hsupport : Function.Surjective own)
    (L : Subgroup (Gamma × Equiv.Perm V))
    (hown : ∀ (a : L) x, own (a.val.2 x) = (a.val.1 : Equiv.Perm U) (own x)) :
    (forget Gamma L).range →* Gamma :=
  (language Gamma L).comp (forgetIso own hsupport L hown).symm.toMonoidHom

theorem languageOnImage_apply (own : V → U) (hsupport : Function.Surjective own)
    (L : Subgroup (Gamma × Equiv.Perm V))
    (hown : ∀ (a : L) x, own (a.val.2 x) = (a.val.1 : Equiv.Perm U) (own x)) (a : L) :
    languageOnImage own hsupport L hown (forgetIso own hsupport L hown a) = a.val.1 := by
  change language Gamma L ((forgetIso own hsupport L hown).symm
    (forgetIso own hsupport L hown a)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- Onto language action requires an actual witness for EVERY component,
as supplied by empty-real-domain requests in ONE fixed decoder. -/
theorem languageOnImage_surjective (own : V → U) (hsupport : Function.Surjective own)
    (L : Subgroup (Gamma × Equiv.Perm V))
    (hown : ∀ (a : L) x, own (a.val.2 x) = (a.val.1 : Equiv.Perm U) (own x))
    (hempty : Function.Surjective (language Gamma L)) :
    Function.Surjective (languageOnImage own hsupport L hown) := by
  intro gamma
  obtain ⟨a,ha⟩ := hempty gamma
  refine ⟨forgetIso own hsupport L hown a,?_⟩
  rw [languageOnImage_apply]
  exact ha

theorem composite_surjective {GammaB : Type w} [Group GammaB]
    (own : V → U) (hsupport : Function.Surjective own)
    (L : Subgroup (Gamma × Equiv.Perm V))
    (hown : ∀ (a : L) x, own (a.val.2 x) = (a.val.1 : Equiv.Perm U) (own x))
    (hempty : Function.Surjective (language Gamma L))
    (quotientAction : Gamma →* GammaB) (honto : Function.Surjective quotientAction) :
    Function.Surjective (quotientAction.comp (languageOnImage own hsupport L hown)) :=
  honto.comp (languageOnImage_surjective own hsupport L hown hempty)

end CCO.FullRows.Semilinear
