import CCO.ParityHasse.Relative.Source

/-! B047 C04/C05: own-identity closure separation and whole quotient kernels.
Every product is actual represented composition; no quotient exact descent
or synthetic diversity identity is introduced. -/

universe u v w t z
namespace CCO.PairSafeSplit.Full
open ParityHasse.Original ParityHasse.Relative
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S) {i : ι}

include H cco in
theorem identity_closure_separation (A B : Rel (X i))
    (hA : Exact S A) (hB : Exact S B) (hAref : ∀ x, A x x) (hBref : ∀ x, B x x)
    (hAB : (fun x y => A x y ∧ B x y) = Eq) :
    (fun x y => closure (⊥ : ColourEq S i).val A x y ∧
      closure (⊥ : ColourEq S i).val B x y) = Eq :=
  identity_separation S H cco A B hA hB hAref hBref hAB

include H cco in
/-- C05 applies to full original K-bisaturated relations and constructs
their actual stable exact equivalence closures. K need not be old equality. -/
theorem kernel_closure_separation (K : ColourEq S i) (hK : Exact S K)
    (A B : Rel (X i)) (hA : Exact S A) (hB : Exact S B)
    (hKA : K ≤ A) (hKB : K ≤ B)
    (satA : Bisaturated K.val A) (satB : Bisaturated K.val B)
    (hAB : (fun x y => A x y ∧ B x y) = K) :
    ∃ CA CB : ColourEq S i, Exact S CA ∧ Exact S CB ∧ CA ⊓ CB = K ∧
      (∃ n, CA = power K.val A n) ∧ (∃ n, CB = power K.val B n) :=
  separated_exact_closures S H cco K hK A B hA hB hKA hKB satA satB hAB

section Pullback
variable {M : Type v} {Q : Type z}

def pullback (π : M → Q) (R : Q → Q → Prop) : M → M → Prop :=
  fun x y => R (π x) (π y)

/-- The actual quotient logical diagonal pulls back to the WHOLE K. -/
theorem quotient_identity (K : Setoid M) : pullback (Quotient.mk K) Eq = K.r := by
  funext x y
  exact propext Quotient.eq

theorem pullback_comp (π : M → Q) (hπ : Function.Surjective π)
    (R T : Q → Q → Prop) :
    pullback π (fun x y => ∃ z, R x z ∧ T z y) =
      (fun x y => ∃ z, pullback π R x z ∧ pullback π T z y) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hR,hT⟩
    obtain ⟨q,rfl⟩ := hπ z
    exact ⟨q,hR,hT⟩
  · rintro ⟨z,hR,hT⟩
    exact ⟨π z,hR,hT⟩

theorem pullback_meet {I : Type*} (π : M → Q) (R : I → Q → Q → Prop) :
    pullback π (fun x y => ∀ n, R n x y) =
      (fun x y => ∀ n, pullback π (R n) x y) := rfl

end Pullback
end CCO.PairSafeSplit.Full
