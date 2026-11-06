import CCO.UnaryFreshFrames.Quotient.Named
import Mathlib.Data.Set.Card
import CCO.UnaryFreshFrames.Examples.TwoCoverBoundary

/-! Source11 C56: an infinite blocks × Bool × infinite-clones model.
The coarse signature has exactly identity/projection term functions and
infinite unforced fibres. Naming the fine bit projection creates an
unforced term with EXACTLY TWO values in a coarse orphan fibre. -/

namespace CCO.TypedOrbitFrames.CoarseBlockBoundary

open CCO.UnaryFreshFrames

abbrev Real := (Nat × Bool) × Nat
abbrev Point := Real ⊕ Nat

def block (x : Real) : Nat := x.1.1
def fine (x : Real) : Nat × Bool := x.1

def language : Language where
  Sorts := Bool
  Func := Unit
  Rel := PEmpty
  input _ := false
  output _ := true
  arity := PEmpty.elim
  argument R := PEmpty.elim R

def sort : Point → Bool
  | .inl _ => false
  | .inr _ => true

def projection : Point → Point
  | .inl x => .inr (block x)
  | .inr q => .inr q

def model : Structure language Point where
  sort := sort
  func _ := projection
  func_sort := by
    rintro _ (x | q) h
    · rfl
    · cases h
  func_offsort := by
    rintro _ (x | q) h
    · exact False.elim (h rfl)
    · rfl
  rel R := PEmpty.elim R
  rel_sort R := PEmpty.elim R

def coarseProjectionTerm : Term language false true :=
  Term.func (L := language) () (Term.id (L := language) false)

theorem coarse_projection_term_value (x : Real) :
    model.eval coarseProjectionTerm (.inl x) = .inr (block x) := rfl

theorem coarse_projection_surjective : Function.Surjective block :=
  fun q => ⟨((q,false),0),rfl⟩

theorem coarse_projection_strict : ¬ Function.Injective block := by
  intro h
  have heq := h (a₁ := ((0,false),0)) (a₂ := ((0,false),1)) rfl
  exact Nat.zero_ne_one (congrArg (fun x : Real => x.2) heq)

def coordinateAut (ρ : Equiv.Perm Nat) (β : Equiv.Perm Bool) (ν : Equiv.Perm Nat) :
    model.Aut := by
  refine ⟨Equiv.sumCongr (Equiv.prodCongr (Equiv.prodCongr ρ β) ν) ρ,?_,?_,?_⟩
  · rintro (x | q) <;> rfl
  · rintro _ (x | q) <;> rfl
  · intro R
    exact PEmpty.elim R

theorem actual_real_sort_transitive (x y : Real) :
    ∃ g : model.Aut, g • (.inl x : Point) = .inl y := by
  refine ⟨coordinateAut (Equiv.swap x.1.1 y.1.1)
    (Equiv.swap x.1.2 y.1.2) (Equiv.swap x.2 y.2),?_⟩
  change (Sum.inl ((Equiv.swap x.1.1 y.1.1 x.1.1,
    Equiv.swap x.1.2 y.1.2 x.1.2),Equiv.swap x.2 y.2 x.2) : Point) = .inl y
  simp

/-- There are no hidden fine-bit operations in the coarse language.
This quantifies over ALL finite actual typed terms, with no length bound. -/
theorem all_real_term_functions {k : language.Sorts} (t : Term language false k) :
    (k = false ∧ ∀ x : Real, model.eval t (.inl x) = .inl x) ∨
    (k = true ∧ ∀ x : Real, model.eval t (.inl x) = .inr (block x)) := by
  induction t with
  | id => exact Or.inl ⟨rfl,fun _ => rfl⟩
  | func F t ih =>
    rcases ih with ⟨_,hId⟩ | ⟨hFalse,_⟩
    · exact Or.inr ⟨rfl,fun x => congrArg projection (hId x)⟩
    · cases hFalse

theorem coarse_semantic_functions_finite :
    {f : Real → Point | ∃ k, ∃ t : Term language false k,
      f = fun x => model.eval t (.inl x)}.Finite := by
  apply ((Set.finite_singleton (fun x : Real => (Sum.inl x : Point))).insert
    (fun x => (Sum.inr (block x) : Point))).subset
  rintro f ⟨k,t,rfl⟩
  rcases all_real_term_functions t with ⟨_,h⟩ | ⟨_,h⟩
  · exact Or.inr (funext h)
  · exact Or.inl (funext h)

theorem real_identity_fibre_infinite (q : Nat) :
    (Quotient.FibreValues block (fun x : Real => (Sum.inl x : Point)) q).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : Nat => (Sum.inl ((q,false),n) : Point))
  · intro n m h
    exact congrArg (fun x : Real => x.2) (Sum.inl.inj h)
  · intro n
    exact ⟨((q,false),n),rfl,rfl⟩

/-- ALL forced coarse terms have an existing named factor on the actual
coarse quotient vertex. Constancy alone is not used as a naming claim. -/
theorem coarse_forced_named_factors {k : language.Sorts} (t : Term language false k)
    (hForced : Quotient.KernelLe block (fun x : Real => model.eval t (.inl x))) :
    ∃ s : Term language true k, ∀ x : Real,
      model.eval t (.inl x) = model.eval s (.inr (block x)) := by
  rcases all_real_term_functions t with ⟨_,hId⟩ | ⟨rfl,hProjection⟩
  · have h := hForced ((0,false),0) ((0,false),1) rfl
    change model.eval t (.inl ((0,false),0)) = model.eval t (.inl ((0,false),1)) at h
    rw [hId,hId] at h
    exact False.elim (Nat.zero_ne_one (congrArg (fun x : Real => x.2) (Sum.inl.inj h)))
  · exact ⟨Term.id (L := language) true,hProjection⟩

/-- EVERY unforced existing coarse term has infinitely many actual values
in EVERY coarse fibre. Adding the fine projection below changes this. -/
theorem coarse_infinite_unforced_indices {k : language.Sorts} (t : Term language false k)
    (hUnforced : ¬ Quotient.KernelLe block (fun x : Real => model.eval t (.inl x)))
    (q : Nat) :
    (Quotient.FibreValues block (fun x : Real => model.eval t (.inl x)) q).Infinite := by
  rcases all_real_term_functions t with ⟨_,hId⟩ | ⟨_,hProjection⟩
  · have hEq : (fun x : Real => model.eval t (.inl x)) = Sum.inl := funext hId
    rw [hEq]
    exact real_identity_fibre_infinite q
  · apply False.elim
    apply hUnforced
    intro x y hxy
    change model.eval t (.inl x) = model.eval t (.inl y)
    rw [hProjection,hProjection,hxy]

theorem fine_unforced_for_coarse : ¬ Quotient.KernelLe block fine := by
  intro h
  have heq := h ((0,false),0) ((0,true),0) rfl
  exact Bool.false_ne_true (congrArg Prod.snd heq)

theorem fine_values_in_coarse_fibre (q : Nat) :
    Quotient.FibreValues block fine q = {(q,false),(q,true)} := by
  ext y
  constructor
  · rintro ⟨⟨⟨p,b⟩,n⟩,h,rfl⟩
    change p = q at h
    subst p
    cases b <;> simp [fine]
  · rintro (rfl | rfl)
    · exact ⟨((q,false),0),rfl,rfl⟩
    · exact ⟨((q,true),0),rfl,rfl⟩

theorem fine_actual_relative_index_two (q : Nat) :
    (Quotient.FibreValues block fine q).ncard = 2 := by
  rw [fine_values_in_coarse_fibre]
  simp

theorem fine_unforced_index_not_infinite (q : Nat) :
    ¬ (Quotient.FibreValues block fine q).Infinite := by
  rw [fine_values_in_coarse_fibre]
  exact Set.Finite.not_infinite ((Set.finite_singleton _).insert _)

/-- The fine projection is also an ACTUAL NAMED TERM in the enlarged
infinite model, not an arbitrary newly considered function. Its coarse
projection has the SAME blocks × Bool × clones real source. -/
theorem named_fine_enrichment_index_two (q : Nat) :
    let T := CCO.UnaryFreshFrames.Examples.TwoCover.originalModel
    let t := CCO.UnaryFreshFrames.Examples.TwoCover.tauTerm
    let p := CCO.UnaryFreshFrames.Examples.TwoCover.pTerm
    (¬ ∀ x y,
      CCO.UnaryFreshFrames.Examples.TwoCover.sort x = 0 →
      CCO.UnaryFreshFrames.Examples.TwoCover.sort y = 0 →
      T.eval p x = T.eval p y → T.eval t x = T.eval t y) ∧
    (CCO.UnaryFreshFrames.Examples.TwoCover.operation 0 ''
      {x | CCO.UnaryFreshFrames.Examples.TwoCover.sort x = 0 ∧
        CCO.UnaryFreshFrames.Examples.TwoCover.operation 2 x =
          CCO.UnaryFreshFrames.Examples.TwoCover.rootPoint q}).ncard = 2 := by
  constructor
  · intro h
    have heq := h
      (CCO.UnaryFreshFrames.Examples.TwoCover.real 0 false 0)
      (CCO.UnaryFreshFrames.Examples.TwoCover.real 0 true 0) rfl rfl rfl
    exact Bool.false_ne_true (congrArg CCO.UnaryFreshFrames.Examples.TwoCover.bit heq)
  · exact CCO.UnaryFreshFrames.Examples.TwoCover.actual_relative_index_two q

end CCO.TypedOrbitFrames.CoarseBlockBoundary
