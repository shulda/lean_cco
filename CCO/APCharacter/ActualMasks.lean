import CCO.APCharacter.SourcePhase
import CCO.APCharacter.Masks
import Mathlib.Tactic.Abel

/-! Literal old-colour masks of the actual reached groupoid character.
Inactive sorts have the single prescribed zero label; old logical equality
is handled separately from the whole gate relation. -/
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

def validBit (_P : SourcePhase S H C A) (i : ι) (ε : Bit) : Prop := ¬Nonempty (Bridge S A i) → ε = 0

def compatible {i j : ι} (ε η : Bit) (x : X i) (y : X j) : Prop :=
  ∀ (hi : Nonempty (Bridge S A i)) (hj : Nonempty (Bridge S A j))
    (R : Arrow S (Reached.kernel H C ⟨i,hi⟩) (Reached.kernel H C ⟨j,hj⟩)),
    R.rel x y → letI := Reached.groupoid H C (A := A); η = ε + P.character.value R

def allows {i j : ι} (c : Option (S.Atom i j)) (ε η : Bit) : Prop :=
  P.validBit i ε ∧ P.validBit j η ∧ ∀ (x : X i) (y : X j),
    S.colour x y = c → P.compatible ε η x y

variable {P}
theorem character_inv {b c : Reached S A}
    (R : Arrow S (Reached.kernel H C b) (Reached.kernel H C c)) :
    letI := Reached.groupoid H C (A := A)
    P.character.value R.inv = -P.character.value R := by
  letI := Reached.groupoid H C (A := A)
  apply eq_neg_iff_add_eq_zero.mpr
  rw [← P.character.map_comp R.inv R]
  change P.character.value (R.inv.comp C R) = 0
  rw [Arrow.inv_comp]
  exact P.character.map_id c

variable (P)
theorem allows_reverse {i j : ι} (a : S.Atom i j) (ε η : Bit) :
    P.allows (some a) ε η ↔ P.allows (some (S.conv a)) η ε := by
  have forward : ∀ {i j} (a : S.Atom i j) (ε η : Bit),
      P.allows (some a) ε η → P.allows (some (S.conv a)) η ε := by
    intro i j a ε η h
    refine ⟨h.2.1,h.1,?_⟩
    intro x y hc hj hi R hR
    letI := Reached.groupoid H C (A := A)
    have hold : S.colour y x = some a := by
      have hh := (S.colour_swap x y (S.conv a)).mp hc
      simpa only [S.conv_invol] using hh
    have he := h.2.2 y x hold hi hj R.inv hR
    rw [character_inv] at he
    apply (eq_add_neg_iff_add_eq).mp at he
    exact he.symm
  constructor
  · exact forward a ε η
  · intro h
    simpa only [S.conv_invol] using forward (S.conv a) η ε h

theorem allows_identity (i : ι) (ε η : Bit) :
    P.allows (i := i) (j := i) none ε η ↔ ε = η ∧ P.validBit i ε := by
  constructor
  · intro h
    refine ⟨?_,h.1⟩
    by_cases hi : Nonempty (Bridge S A i)
    · let b : Reached S A := ⟨i,hi⟩
      let x := Classical.choice (S.nonemptySort i)
      have hc : S.colour x x = none := (S.colour_none_iff x x).mpr rfl
      have he := h.2.2 x x hc hi hi (Arrow.id (Reached.kernel H C b))
        ((Reached.kernel H C b).setoid.refl x)
      letI := Reached.groupoid H C (A := A)
      have hz : P.character.value (Arrow.id (Reached.kernel H C b)) = 0 := P.character.map_id b
      rw [hz,add_zero] at he
      exact he.symm
    · exact (h.1 hi).trans (h.2.1 hi).symm
  · rintro ⟨rfl,hε⟩
    refine ⟨hε,hε,?_⟩
    intro x y hc hi hj R hR
    have hxy : x = y := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using (S.colour_none_iff x y).mp hc
    subst y
    have hid : R = Arrow.id (Reached.kernel H C ⟨i,hi⟩) :=
      R.eq_of_common_real_pair H _ hR ((Reached.kernel H C ⟨i,hi⟩).setoid.refl x)
    letI := Reached.groupoid H C (A := A)
    have hz : P.character.value (Arrow.id (Reached.kernel H C ⟨i,hi⟩)) = 0 :=
      P.character.map_id (⟨i,hi⟩ : Reached S A)
    rw [hid,hz,add_zero]

/-- One actual pair suffices: all rigid bridge relations are unions of old
pair orbitals. This retains the fine optional colour, including equality. -/
theorem compatible_of_colour {i j : ι} {ε η : Bit} {x x' : X i} {y y' : X j}
    (h : P.compatible ε η x y) (hc : S.colour x y = S.colour x' y') :
    P.compatible ε η x' y' := by
  intro hi hj R hR
  obtain ⟨g,hgx,hgy⟩ := (S.pair_homogeneous_of_homogeneous H) x' x y' y hc.symm
  have hr : R.rel x y := by
    simpa only [hgx,hgy] using R.exact.invariant S H g x' y' hR
  exact h hi hj R hr

theorem allows_actual_iff {i j : ι} (x : X i) (y : X j) (ε η : Bit) :
    P.allows (S.colour x y) ε η ↔
      P.validBit i ε ∧ P.validBit j η ∧ P.compatible ε η x y := by
  constructor
  · intro h
    exact ⟨h.1,h.2.1,h.2.2 x y rfl⟩
  · rintro ⟨hε,hη,h⟩
    exact ⟨hε,hη,fun x' y' hc => P.compatible_of_colour h hc.symm⟩


def masks : MaskData S where
  validBit := P.validBit
  allowed := P.allows
  reverse := P.allows_reverse
  identity := P.allows_identity

theorem original_global_marking
    (mark : Reached.Point H C A → Bit)
    (hm : letI := Reached.groupoid H C (A := A)
      Abstract.IsMarking (Reached.pointFunctor H C A) P.character mark) :
    P.masks.GlobalMarking (originalMarking S H C A mark) := by
  constructor
  · rintro ⟨i,x⟩ hi
    simp only [originalMarking,dif_neg hi]
  · rintro ⟨i,x⟩ ⟨j,y⟩
    apply (P.allows_actual_iff x y _ _).mpr
    refine ⟨?_,?_,?_⟩
    · intro hi
      simp only [originalMarking,dif_neg hi]
    · intro hj
      simp only [originalMarking,dif_neg hj]
    · intro hi hj R hR
      exact originalMarking_arrow_equation S H C A P.character mark hm R x y hR


end SourcePhase
end
end CCO.APCharacter
