import CCO.AclOwners.AclCore
import CCO.AclOwners.Avoidance

/-! Ordinary closed-base avoidance for arbitrary actions. This is the
second padding realignment and needs no owner harmlessness at all. -/
universe v t
namespace CCO.MIGeometry
open RealClosure.Bounds AclOwners
variable {M : Type v} {G : Type t} [Group G] [MulAction G M]

def realBaseFixer (A : Finset M) : Subgroup G where
  carrier := {g | ∀ a ∈ A, g • a = a}
  one_mem' := fun _ _ => one_smul _ _
  mul_mem' := by
    intro g h hg hh a ha
    rw [mul_smul,hh a ha,hg a ha]
  inv_mem' := by
    intro g hg a ha
    rw [inv_smul_eq_iff,hg a ha]

theorem realBaseFixer_orbit (A : Finset M) (x : M) :
    MulAction.orbit (realBaseFixer (G := G) A) x = orbitOver G A x := by
  ext y
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g.val,g.property,rfl⟩
  · rintro ⟨g,hg,rfl⟩
    exact ⟨⟨g,hg⟩,rfl⟩

/-- Finite extensions can be moved off any finite forbidden set away
from an absolutely closed fixed base, by ONE actual group element. -/
theorem closed_base_avoidance [DecidableEq M] (A L Z : Finset M)
    (closed : Closed G A) :
    ∃ g : G, (∀ a ∈ A, g • a = a) ∧
      ∀ x ∈ L, x ∉ A → ∀ z ∈ Z, g • x ≠ z := by
  classical
  have hi (x : M) (hx : x ∈ L \ A) :
      (MulAction.orbit (realBaseFixer (G := G) A) x).Infinite := by
    rw [realBaseFixer_orbit]
    intro hf
    have ha : x ∈ Acl G A := hf
    rw [closed] at ha
    exact (Finset.mem_sdiff.mp hx).2 ha
  obtain ⟨g,hg⟩ := finite_action_avoidance (G := realBaseFixer (G := G) A) (L \ A) Z hi
  exact ⟨g.val,g.property,fun x hx hxA z hz => hg x (Finset.mem_sdiff.mpr ⟨hx,hxA⟩) z hz⟩

end CCO.MIGeometry
