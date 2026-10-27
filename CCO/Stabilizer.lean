import CCO.Finite
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Pointwise stabilizers of finite real bases

The stabilizer acts on the tagged real universe, so distinct named sorts
remain disjoint. A stabilizer fixes a SET of real values, rather than an
injectively indexed neighbour list. This distinction is crucial for the
later collision-removal argument, where neighbour images may coincide.
-/

universe u v

namespace CCO.RealAction

variable {ι : Type u} {X : ι → Type v}
variable {G : Type*} [Group G] [MulAction G (Sigma X)]

/-- The actual pointwise stabilizer of an arbitrary set of tagged real
points. Finite bases are handled using the same definition. -/
def pointwiseStabilizer (B : Set (Sigma X)) : Subgroup G where
  carrier := {g | ∀ b ∈ B, g • b = b}
  one_mem' := by
    intro b hb
    exact one_smul G b
  mul_mem' := by
    intro g h hg hh b hb
    rw [mul_smul, hh b hb, hg b hb]
  inv_mem' := by
    intro g hg b hb
    have h := congrArg (fun x => g⁻¹ • x) (hg b hb)
    simpa only [inv_smul_smul] using h.symm

theorem mem_pointwiseStabilizer (B : Set (Sigma X)) (g : G) :
    g ∈ pointwiseStabilizer (G := G) B ↔ ∀ b ∈ B, g • b = b :=
  Iff.rfl

/-- Real orbit under the group fixing B pointwise. -/
def orbitOver (B : Set (Sigma X)) (x : Sigma X) : Set (Sigma X) :=
  { y | ∃ g : G, g ∈ pointwiseStabilizer (G := G) B ∧ g • x = y }

theorem self_mem_orbitOver (B : Set (Sigma X)) (x : Sigma X) :
    x ∈ orbitOver (G := G) B x := by
  exact ⟨1, Subgroup.one_mem _, one_smul G x⟩

theorem orbitOver_fixed_base (B : Set (Sigma X)) (x : Sigma X)
    (hx : x ∈ B) :
    orbitOver (G := G) B x = {x} := by
  ext y
  constructor
  · rintro ⟨g, hg, hgy⟩
    have hfix := (mem_pointwiseStabilizer B g).mp hg x hx
    exact Set.mem_singleton_iff.mpr (hgy ▸ hfix.symm)
  · intro hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact self_mem_orbitOver B x

/-- An orbit of a point outside B cannot meet B. -/
theorem orbitOver_disjoint_base (B : Set (Sigma X)) (x : Sigma X)
    (hx : x ∉ B) :
    Disjoint (orbitOver (G := G) B x) B := by
  apply Set.disjoint_left.mpr
  intro y hy hB
  rcases hy with ⟨g, hg, hgy⟩
  have hfix := (mem_pointwiseStabilizer B g).mp hg y hB
  have hyx : x = y := by
    have h := congrArg (fun z => g⁻¹ • z) hgy
    have h' := congrArg (fun z => g⁻¹ • z) hfix
    simp only [inv_smul_smul] at h h'
    calc
      x = g⁻¹ • y := h
      _ = y := h'
  exact hx (hyx ▸ hB)

/-- The elementary fixed-set monotonicity used when a neighbour-image
base grows during an injectivization recursion. -/
theorem stabilizer_antitone {B C : Set (Sigma X)} (h : B ⊆ C) :
    pointwiseStabilizer (G := G) C ≤ pointwiseStabilizer (G := G) B := by
  intro g hg b hb
  exact (mem_pointwiseStabilizer C g).mp hg b (h hb)

end CCO.RealAction
