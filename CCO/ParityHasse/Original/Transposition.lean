import CCO.ParityHasse.Original.Equivalences
import Mathlib.Order.ModularLattice

/-!
# Transposition: interval order and actual classes are separate constructions

The quotient map below sends the class of a real point to its class for the
larger kernel. Surjectivity uses the represented product formula for the join;
it is not inferred from the abstract modular interval isomorphism.
-/

universe u v

namespace CCO.ParityHasse.Original

variable {A : Type u}

/-- The natural map on classes, induced by inclusion of the actual X-class. -/
def transpositionClassMap (E X : Setoid A) (a : A) :
    RelativeClass (E ⊓ X) X a → RelativeClass E (E ⊔ X) a :=
  Quotient.lift (fun x : {x // X a x} =>
    Quotient.mk _ (⟨x.val, (show X ≤ E ⊔ X from le_sup_right) x.property⟩ :
      {x // (E ⊔ X) a x})) (by
        intro x y h
        exact Quotient.sound h.1)

theorem transpositionClassMap_injective (E X : Setoid A) (a : A) :
    Function.Injective (transpositionClassMap E X a) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro x y h
  apply Quotient.sound
  simp only [transpositionClassMap, Quotient.lift_mk] at h
  have he := Quotient.exact h
  exact ⟨he, X.trans (X.symm x.property) y.property⟩

theorem transpositionClassMap_surjective (E X : Setoid A)
    (hjoin : ∀ x y, (E ⊔ X) x y ↔ ∃ z, X x z ∧ E z y) (a : A) :
    Function.Surjective (transpositionClassMap E X a) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro y
  obtain ⟨z, hz, hzy⟩ := (hjoin a y.val).mp y.property
  refine ⟨Quotient.mk _ (⟨z, hz⟩ : {x // X a x}), ?_⟩
  exact Quotient.sound hzy

/-- A genuine bijection of relative equivalence classes of real points. -/
noncomputable def relativeClassTransposition (E X : Setoid A)
    (hjoin : ∀ x y, (E ⊔ X) x y ↔ ∃ z, X x z ∧ E z y) (a : A) :
    RelativeClass (E ⊓ X) X a ≃ RelativeClass E (E ⊔ X) a :=
  Equiv.ofBijective (transpositionClassMap E X a)
    ⟨transpositionClassMap_injective E X a,
      transpositionClassMap_surjective E X hjoin a⟩

/-- Relative index equality follows from the actual class bijection. -/
theorem relativeIndex_transposition (E X : Setoid A)
    (hjoin : ∀ x y, (E ⊔ X) x y ↔ ∃ z, X x z ∧ E z y) (a : A) :
    relativeIndex (E ⊓ X) X a = relativeIndex E (E ⊔ X) a :=
  Nat.card_congr (relativeClassTransposition E X hjoin a)

/-- The lattice-theoretic interval isomorphism, independently of class counts. -/
def intervalTransposition {L : Type v} [Lattice L] [IsModularLattice L] (E X : L) :
    Set.Icc (E ⊓ X) X ≃o Set.Icc E (E ⊔ X) :=
  infIccOrderIsoIccSup' E X

theorem transposition_cover_iff {L : Type v} [Lattice L] [IsModularLattice L]
    (E X : L) : E ⊓ X ⋖ X ↔ E ⋖ E ⊔ X :=
  ⟨covBy_sup_of_inf_covBy_right, inf_covBy_of_covBy_sup_left⟩

end CCO.ParityHasse.Original
