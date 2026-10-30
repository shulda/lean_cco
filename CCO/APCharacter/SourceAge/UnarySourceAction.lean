import CCO.APCharacter.SourceAge.UnarySource
import Mathlib.Algebra.Group.ULift

/-! The acting group is the FULL automorphism group of the entire actual
marked limit, transported to all canonical child sorts simultaneously.
No childwise homogeneity or arbitrary subgroup replaces that whole action. -/
universe u v w t
open scoped FirstOrder
namespace CCO.APCharacter.SourceAge.UnarySource
open OwnerTransversal.CountableColour
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {M : MaskData S}
variable {completion : Age.CompletionProperty S M}
noncomputable section
variable (I : Identification S H completion)

abbrev NewPoint := Sigma (Rank.Point (β I) (tag I))
instance limitAutGroup : Group (Age.Limit S H completion ≃[Age.Language S] Age.Limit S H completion) where
  mul f g := f.comp g
  mul_assoc _ _ _ := rfl
  one := FirstOrder.Language.Equiv.refl _ _
  one_mul _ := rfl
  mul_one _ := rfl
  inv f := f.symm
  inv_mul_cancel f := FirstOrder.Language.Equiv.symm_comp_self f

abbrev FullGroup (_I : Identification S H completion) := ULift.{t} (Age.Limit S H completion ≃[Age.Language S] Age.Limit S H completion)

def oldEquiv : NewPoint I ≃ Sigma X where
  toFun := Rank.forget (β I) (tag I)
  invFun p := ⟨⟨p.1,tag I p.1 p.2⟩,⟨p.2,rfl⟩⟩
  left_inv := by
    rintro ⟨⟨i,b⟩,⟨x,hx⟩⟩
    apply Rank.forget_injective (β I) (tag I)
    rfl
  right_inv p := by cases p; rfl

def newEquiv : NewPoint I ≃ Age.Limit S H completion := (oldEquiv I).trans I.equiv

def childLabel (c : Rank.Child (β I)) : ι × Bit := (c.1,c.2.val)
theorem childLabel_injective : Function.Injective (childLabel I) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ he
  have hij : i=j := congrArg Prod.fst he
  subst j
  have hbc : b=c := Subtype.ext (congrArg Prod.snd he)
  subst c
  rfl

theorem new_owner (p : NewPoint I) :
    (Age.limitCoding S H completion).table.owner (newEquiv I p) = Age.ownerEquiv S (childLabel I p.1) := by
  rcases p with ⟨⟨i,b⟩,⟨x,hx⟩⟩
  change (Age.limitCoding S H completion).table.owner (I.equiv ⟨i,x⟩) = Age.ownerEquiv S (i,b.val)
  rw [owner_eq]
  exact congrArg (Age.ownerEquiv S) (Prod.ext rfl (congrArg Subtype.val hx))

theorem full_owner (g : FullGroup I) (y : Age.Limit S H completion) :
    (Age.limitCoding S H completion).table.owner (g.down y) =
      (Age.limitCoding S H completion).table.owner y :=
  ((Age.limitCoding S H completion).embedding_preserves (Age.limitCoding S H completion) g.down.toEmbedding).1 y

theorem full_colour (g : FullGroup I) (y z : Age.Limit S H completion) :
    (Age.limitCoding S H completion).table.colour (g.down y) (g.down z) =
      (Age.limitCoding S H completion).table.colour y z :=
  ((Age.limitCoding S H completion).embedding_preserves (Age.limitCoding S H completion) g.down.toEmbedding).2 y z

def move (g : FullGroup I) (p : NewPoint I) : NewPoint I :=
  (newEquiv I).symm (g.down (newEquiv I p))

theorem move_image (g : FullGroup I) (p : NewPoint I) :
    newEquiv I (move I g p) = g.down (newEquiv I p) := (newEquiv I).apply_symm_apply _

theorem move_child (g : FullGroup I) (p : NewPoint I) : (move I g p).1 = p.1 := by
  apply childLabel_injective I
  apply (Age.ownerEquiv S).injective
  rw [← new_owner I,← new_owner I,move_image,full_owner]

def pointMove {c : Rank.Child (β I)} (g : FullGroup I) (x : Rank.Point (β I) (tag I) c) :
    Rank.Point (β I) (tag I) c :=
  cast (congrArg (Rank.Point (β I) (tag I)) (move_child I g ⟨c,x⟩)) (move I g ⟨c,x⟩).2

theorem sigma_cast {J : Type*} {P : J → Type*} {a b : J} (h : a=b) (x : P a) :
    (⟨b,cast (congrArg P h) x⟩ : Sigma P) = ⟨a,x⟩ := by cases h; rfl

theorem pointMove_sigma {c : Rank.Child (β I)} (g : FullGroup I) (x : Rank.Point (β I) (tag I) c) :
    (⟨c,pointMove I g x⟩ : NewPoint I) = move I g ⟨c,x⟩ :=
  sigma_cast (move_child I g ⟨c,x⟩) (move I g ⟨c,x⟩).2

theorem pointMove_image {c : Rank.Child (β I)} (g : FullGroup I) (x : Rank.Point (β I) (tag I) c) :
    newEquiv I ⟨c,pointMove I g x⟩ = g.down (newEquiv I ⟨c,x⟩) := by
  rw [pointMove_sigma,move_image]

theorem child_embedding_injective (c : Rank.Child (β I)) :
    Function.Injective (fun x : Rank.Point (β I) (tag I) c => newEquiv I ⟨c,x⟩) := by
  intro x y he
  exact eq_of_heq (Sigma.mk.inj_iff.mp ((newEquiv I).injective he)).2

noncomputable instance childAction (c : Rank.Child (β I)) : MulAction (FullGroup I) (Rank.Point (β I) (tag I) c) where
  smul := pointMove I
  one_smul x := by
    apply child_embedding_injective I c
    change newEquiv I ⟨c,pointMove I 1 x⟩ = newEquiv I ⟨c,x⟩
    rw [pointMove_image]
    rfl
  mul_smul g h x := by
    apply child_embedding_injective I c
    change newEquiv I ⟨c,pointMove I (g*h) x⟩ = newEquiv I ⟨c,pointMove I g (pointMove I h x)⟩
    rw [pointMove_image,pointMove_image,pointMove_image]
    rfl

theorem smul_image (g : FullGroup I) (p : NewPoint I) :
    newEquiv I (g • p) = g.down (newEquiv I p) := by
  rcases p with ⟨c,x⟩
  exact pointMove_image I g x

end
end CCO.APCharacter.SourceAge.UnarySource
