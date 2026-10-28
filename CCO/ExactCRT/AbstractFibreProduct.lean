import CCO.ExactCRT.AbstractCRT

/-! B008 C17: the two-factor set bijection only needs represented
commutation, independently of class Helly and distributivity. -/

namespace CCO.ExactCRT.Abstract
variable {A : Type*}

def FibreProduct (E F : Setoid A) :=
  {p : Quotient E × Quotient F //
    quotientMap (show E ≤ E ⊔ F from le_sup_left) p.1 =
      quotientMap (show F ≤ E ⊔ F from le_sup_right) p.2}

def fibreCoordinates (E F : Setoid A) (q : Quotient (E ⊓ F)) : FibreProduct E F := by
  refine ⟨(quotientMap inf_le_left q, quotientMap inf_le_right q), ?_⟩
  induction q using Quotient.inductionOn with
  | _ x => rfl

@[simp] theorem fibreCoordinates_mk (E F : Setoid A) (x : A) :
    (fibreCoordinates E F (Quotient.mk _ x)).val =
      (Quotient.mk E x, Quotient.mk F x) := rfl

theorem fibreCoordinates_injective (E F : Setoid A) :
    Function.Injective (fibreCoordinates E F) := by
  intro q r h
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      have hp := congrArg Subtype.val h
      exact ⟨Quotient.exact (congrArg Prod.fst hp), Quotient.exact (congrArg Prod.snd hp)⟩

theorem fibreCoordinates_surjective (E F : Setoid A) (comm : Permutes E F) :
    Function.Surjective (fibreCoordinates E F) := by
  rintro ⟨⟨p, q⟩, hpq⟩
  induction p using Quotient.inductionOn with
  | _ x =>
    induction q using Quotient.inductionOn with
    | _ y =>
      obtain ⟨z, hxz, hyz⟩ := (quotient_images_eq_iff E F comm x y).mp hpq
      refine ⟨Quotient.mk _ z, ?_⟩
      apply Subtype.ext
      exact Prod.ext (Quotient.sound (E.symm hxz)) (Quotient.sound (F.symm hyz))

noncomputable def fibreProductEquiv (E F : Setoid A) (comm : Permutes E F) :
    Quotient (E ⊓ F) ≃ FibreProduct E F :=
  Equiv.ofBijective _ ⟨fibreCoordinates_injective E F, fibreCoordinates_surjective E F comm⟩

@[simp] theorem fibreProductEquiv_apply (E F : Setoid A) (comm : Permutes E F) (x : A) :
    (fibreProductEquiv E F comm (Quotient.mk _ x)).val =
      (Quotient.mk E x, Quotient.mk F x) := rfl

end CCO.ExactCRT.Abstract
