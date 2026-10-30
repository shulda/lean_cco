import CCO.APCharacter.SeedSource
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Actual source witnesses for the nonempty children and the old diversity
colour lost in BOTH equal-phase children. No marked homogeneity is assumed. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
namespace SourcePhase
variable (P : SourcePhase S H C A)

theorem bit_eq_or_add_one (ε δ : Bit) : ε = δ ∨ ε = δ+1 := by
  classical
  fin_cases ε <;> fin_cases δ
  · exact Or.inl rfl
  · exact Or.inr (ZModModule.add_self (1 : Bit)).symm
  · exact Or.inr (zero_add (1 : Bit)).symm
  · exact Or.inl rfl

theorem actual_two_children :
    ∃ mark : Sigma X → Bit, P.masks.GlobalMarking mark ∧
      ∀ (b : Reached S A) (ε : Bit), ∃ x : X b.val, mark ⟨b.val,x⟩ = ε := by
  obtain ⟨m,hm⟩ := actual_global_marking S H C A P.character
  let mark := originalMarking S H C A m
  refine ⟨mark,P.original_global_marking m hm,?_⟩
  intro b ε
  let x : X b.val := Classical.choice (S.nonemptySort b.val)
  let y := (P.atSort b).pointImage H x
  have hxy : (P.atSort b).rel x y := (P.atSort b).pointImage_spec H x
  have he : mark ⟨b.val,y⟩ = mark ⟨b.val,x⟩ + 1 := by
    have hh := originalMarking_arrow_equation S H C A P.character m hm (P.atSort b) x y hxy
    rw [P.atSort_detects] at hh
    exact hh
  rcases bit_eq_or_add_one ε (mark ⟨b.val,x⟩) with h | h
  · exact ⟨x,h.symm⟩
  · exact ⟨y,he.trans h.symm⟩

theorem actual_lost_atom (b : Reached S A) :
    ∃ a : S.Atom b.val b.val,
      (∃ x y, S.colour x y = some a) ∧ ∀ ε : Bit, ¬P.allows (some a) ε ε := by
  let T := P.atSort b
  obtain ⟨x,y,hxy⟩ := T.exact.nonempty S
  have hc : S.colour x y ≠ none := by
    intro hc
    have he : x = y := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using (S.colour_none_iff x y).mp hc
    subst y
    exact P.atSort_nonidentity b (T.eq_of_common_real_pair H (Arrow.id _) hxy
      ((Reached.kernel H C b).setoid.refl x))
  obtain ⟨a,ha⟩ := Option.ne_none_iff_exists'.mp hc
  refine ⟨a,⟨x,y,ha⟩,?_⟩
  intro ε h
  letI := Reached.groupoid H C (A := A)
  have he := h.2.2 x y ha b.property b.property T hxy
  have ht : P.character.value T = 1 := P.atSort_detects b
  have he' : ε = ε + 1 := he.trans (congrArg (fun a => ε+a) ht)
  have hzero : (0 : Bit) = 1 := add_left_cancel ((add_zero ε).trans he')
  exact zero_ne_one hzero

end SourcePhase
end
end CCO.APCharacter
