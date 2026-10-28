import CCO.RigidGroupoid.Phase.AbstractMarkings
import Mathlib.Data.Finset.Basic

/-! Literal finite prescribed-point sets, orbit-wise independent bits and
empty/singleton controls. These are functions, not source automorphisms. -/

universe u v w
namespace CCO.RigidGroupoid.Phase.Abstract
open CategoryTheory
noncomputable section
variable {J : Type u} [Groupoid.{v} J] (F : J ⥤ Type w)

def shiftByOrbits (mark : Point F → Bit) (σ : OrbitClass F → Bit) : Point F → Bit :=
  fun p => mark p + σ (pointClass F p)

theorem shiftByOrbits_isMarking (χ : Character J) {mark : Point F → Bit}
    (hm : IsMarking F χ mark) (σ : OrbitClass F → Bit) :
    IsMarking F χ (shiftByOrbits F mark σ) := by
  intro a b R q
  have hc : pointClass F (⟨b,F.map R q⟩ : Point F) = pointClass F ⟨a,q⟩ :=
    (class_eq_iff F).mpr (orbit_symm F ⟨R,rfl⟩)
  simp only [shiftByOrbits, hm R q, hc]
  abel

/-- Points in different actual action orbits can receive either prescribed
phase difference, by changing the seed of only one orbit. -/
theorem different_orbits_both_differences (free : Free F) (χ : Character J)
    (p q : Point F) (hne : ¬ Orbit F p q) (δ : Bit) :
    ∃ mark, IsMarking F χ mark ∧ mark q = mark p + δ := by
  classical
  obtain ⟨mark, hm⟩ := exists_marking F free χ
  have hc : pointClass F p ≠ pointClass F q := fun h => hne ((class_eq_iff F).mp h)
  let σ : OrbitClass F → Bit := fun z => if z = pointClass F q then δ - mark q + mark p else 0
  refine ⟨shiftByOrbits F mark σ, shiftByOrbits_isMarking F χ hm σ, ?_⟩
  simp only [shiftByOrbits, σ, if_pos rfl, if_neg hc, add_zero]
  abel

/-- A rigid transport forces its character difference in EVERY compatible
marking, while the preceding result concerns suitable global choices. -/
theorem rigid_difference (χ : Character J) {mark : Point F → Bit}
    (hm : IsMarking F χ mark) {a b : J} (R : a ⟶ b) (q : F.obj a) :
    mark ⟨b,F.map R q⟩ - mark ⟨a,q⟩ = χ.value R := by
  rw [hm R q]
  abel

theorem singleton_extends (free : Free F) (χ : Character J) (p : Point F) (ε : Bit) :
    ∃ mark, IsMarking F χ mark ∧ mark p = ε := by
  obtain ⟨mark, hm⟩ := exists_marking F free χ
  refine ⟨shiftByOrbits F mark (fun _ => ε - mark p),
    shiftByOrbits_isMarking F χ hm _, ?_⟩
  dsimp [shiftByOrbits]
  abel

def extendFiniteBits (s : Finset (Point F)) (ε : s → Bit) (p : Point F) : Bit := by
  classical
  exact if hp : p ∈ s then ε ⟨p,hp⟩ else 0

theorem extendFiniteBits_spec (s : Finset (Point F)) (ε : s → Bit) (p : s) :
    extendFiniteBits F s ε p = ε p := by
  classical
  simp [extendFiniteBits, p.property]

/-- C30 on an actual finite SET, with bits a genuine function on that set.
Thus repeated real presentations must first descend consistently to points. -/
theorem finite_seed_extension_iff (free : Free F) (χ : Character J)
    (s : Finset (Point F)) (ε : s → Bit) :
    (∃ mark, IsMarking F χ mark ∧ ∀ p : s, mark p = ε p) ↔
      ∀ (p q : s) (R : p.val.1 ⟶ q.val.1),
        F.map R p.val.2 = q.val.2 → ε q = ε p + χ.value R := by
  classical
  constructor
  · rintro ⟨mark, hm, he⟩ p q R hR
    have hpt : (⟨q.val.1, F.map R p.val.2⟩ : Point F) = q.val :=
      congrArg (Sigma.mk q.val.1) hR
    have h := hm R p.val.2
    rw [hpt, he, he] at h
    exact h
  · intro he
    let e := extendFiniteBits F s ε
    have hc : SeedCompatible F χ (↑s) e := by
      intro a b R q hp hq
      change (⟨a,q⟩ : Point F) ∈ s at hp
      change (⟨b,F.map R q⟩ : Point F) ∈ s at hq
      have h := he ⟨⟨a,q⟩,hp⟩ ⟨⟨b,F.map R q⟩,hq⟩ R rfl
      change extendFiniteBits F s ε ⟨b,F.map R q⟩ =
        extendFiniteBits F s ε ⟨a,q⟩ + χ.value R
      calc
        _ = ε ⟨⟨b,F.map R q⟩,hq⟩ := extendFiniteBits_spec F s ε _
        _ = ε ⟨⟨a,q⟩,hp⟩ + χ.value R := h
        _ = _ := congrArg (· + χ.value R) (extendFiniteBits_spec F s ε ⟨⟨a,q⟩,hp⟩).symm
    obtain ⟨mark, hm, hext⟩ := (exists_marking_extends_iff F free χ (↑s) e).mpr hc
    refine ⟨mark, hm, ?_⟩
    intro p
    exact (hext p p.property).trans (extendFiniteBits_spec F s ε p)

theorem finite_restriction (free : Free F) (χ : Character J) (s : Finset (Point F)) :
    ∃ mark, IsMarking F χ mark ∧ ∃ ε : s → Bit, ∀ p : s, ε p = mark p := by
  obtain ⟨mark, hm⟩ := exists_marking F free χ
  exact ⟨mark, hm, (fun p => mark p), fun _ => rfl⟩

theorem empty_seed_extends (free : Free F) (χ : Character J)
    (ε : (∅ : Finset (Point F)) → Bit) :
    ∃ mark, IsMarking F χ mark ∧ ∀ p : (∅ : Finset (Point F)), mark p = ε p := by
  obtain ⟨mark, hm⟩ := exists_marking F free χ
  exact ⟨mark, hm, fun p => False.elim (Finset.notMem_empty p.val p.property)⟩

end
end CCO.RigidGroupoid.Phase.Abstract
