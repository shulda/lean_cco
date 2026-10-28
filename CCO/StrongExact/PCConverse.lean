import CCO.StrongExact.FinitePC

/-!
# C10: converse compatibility and all-coordinate STRONG PC support

The current Boolean PC network ranges only over genuinely distinct
formal vertex pairs. The source's bidirectional atomic edge coherence
ensures the initial network is converse closed. The simultaneous
three-distinct-vertex pruning respects this involution because the
actual STRONG triangle product commutes with typed converse.

Consequently the greatest finite fixed point satisfies the FULL
three-coordinate PC predicate on every triple of distinct formal
vertices, even when two or all three of their named sorts coincide.
No SAP/CCO or positive-menu exactness is needed here.
-/

universe u v w z

namespace CCO.StrongPC

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u, v, w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

def ConverseClosed (N : Network D) : Prop :=
  ∀ p : DistinctPair V,
    N ⟨p.dst, p.src, p.ne.symm⟩ = S.opposite (N p)

theorem initial_converse : ConverseClosed D (initial D) := by
  intro p
  cases h : D.edge p.src p.dst p.ne with
  | none =>
      have hr : D.edge p.dst p.src p.ne.symm = none := by
        cases hb : D.edge p.dst p.src p.ne.symm with
        | none => rfl
        | some b =>
            have hf := (D.edge_reverse p.dst p.src p.ne.symm b).mp hb
            rw [h] at hf
            cases hf
      ext a
      simp [initial, h, hr, AtomicSource.opposite]
  | some a =>
      have hr := (D.edge_reverse p.src p.dst p.ne a).mp h
      have hLeft : initial D ⟨p.dst, p.src, p.ne.symm⟩ =
          ({S.conv a} : S.Menu (D.vertexSort p.dst) (D.vertexSort p.src)) := by
        simp [initial, hr]
      have hRight : initial D p =
          ({a} : S.Menu (D.vertexSort p.src) (D.vertexSort p.dst)) := by
        simp [initial, h]
      rw [hLeft, hRight]
      ext b
      change b = S.conv a ↔ S.conv b = a
      constructor
      · intro hb
        subst b
        exact S.conv_invol a
      · intro hb
        have h' := congrArg (fun c => S.conv c) hb
        simpa only [S.conv_invol] using h'

/-- The reverse of an updated reversed pair's domain is contained in
the forward updated domain; full equality follows by swapping pairs. -/
private theorem step_converse_half
    (N : Network D) (hConv : ConverseClosed D N)
    (p : DistinctPair V) :
    step D N ⟨p.dst, p.src, p.ne.symm⟩ ⊆
      S.opposite (step D N p) := by
  intro a ha
  change S.conv a ∈ step D N p
  constructor
  · have h : a ∈ N ⟨p.dst, p.src, p.ne.symm⟩ := ha.1
    rw [hConv p] at h
    exact h
  · intro z hxz hzy
    have hyz : p.dst ≠ z := hzy.symm
    have hzx : z ≠ p.src := hxz.symm
    have hProd : a ∈ S.product
        (N ⟨p.dst, z, hyz⟩) (N ⟨z, p.src, hzx⟩) :=
      ha.2 z hyz hzx
    have hOpp : S.conv a ∈ S.opposite
        (S.product (N ⟨p.dst, z, hyz⟩)
          (N ⟨z, p.src, hzx⟩)) := by
      change S.conv (S.conv a) ∈ S.product
        (N ⟨p.dst, z, hyz⟩) (N ⟨z, p.src, hzx⟩)
      simpa only [S.conv_invol] using hProd
    rw [S.product_opposite] at hOpp
    have hzxConv := hConv ⟨z, p.src, hzx⟩
    have hyzConv := hConv ⟨p.dst, z, hyz⟩
    rw [← hzxConv, ← hyzConv] at hOpp
    exact hOpp

theorem step_converse
    (N : Network D) (hConv : ConverseClosed D N) :
    ConverseClosed D (step D N) := by
  intro p
  apply Set.Subset.antisymm
  · exact step_converse_half D N hConv p
  · intro a ha
    have h : S.conv a ∈ step D N p := ha
    have hBack := step_converse_half D N hConv
      ⟨p.dst, p.src, p.ne.symm⟩ h
    change S.conv (S.conv a) ∈
      step D N ⟨p.dst, p.src, p.ne.symm⟩ at hBack
    simpa only [S.conv_invol] using hBack

theorem iterate_converse (N : Network D)
    (hConv : ConverseClosed D N) (n : Nat) :
    ConverseClosed D (iterate D N n) := by
  induction n with
  | zero => exact hConv
  | succ n ih => exact step_converse D _ ih

theorem fixedNetwork_converse :
    ConverseClosed D (fixedNetwork D) :=
  iterate_converse D (initial D) (initial_converse D) (fixedIndex D)

/-- Stable STRONG support on the output pair of every formal triangle. -/
theorem stable_triangle_support (N : Network D)
    (hStable : Stable D N)
    {x y z : V} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    N ⟨x, z, hxz⟩ ⊆
      S.product (N ⟨x, y, hxy⟩) (N ⟨y, z, hyz⟩) := by
  intro a ha
  have hs : a ∈ step D N ⟨x, z, hxz⟩ := by
    rw [hStable ⟨x, z, hxz⟩]
    exact ha
  exact hs.2 y hxy hyz

/-- A stable converse-compatible network satisfies all three PC
support inclusions, never just the output-coordinate inclusion. -/
theorem stable_PC (N : Network D)
    (hStable : Stable D N) (hConv : ConverseClosed D N)
    {x y z : V} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    S.PC (N ⟨x, y, hxy⟩)
      (N ⟨y, z, hyz⟩) (N ⟨x, z, hxz⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · exact stable_triangle_support D N hStable hxy hyz hxz
  · have h := stable_triangle_support D N hStable hxz hyz.symm hxy
    rw [hConv ⟨y, z, hyz⟩] at h
    exact h
  · have h := stable_triangle_support D N hStable hxy.symm hxz hyz
    rw [hConv ⟨x, y, hxy⟩] at h
    exact h

/-- Every actual finite PC fixed network has three-coordinate strong
path consistency on each triple of distinct vertices, without SAP or CCO. -/
theorem fixedNetwork_PC {x y z : V}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    S.PC (fixedNetwork D ⟨x, y, hxy⟩)
      (fixedNetwork D ⟨y, z, hyz⟩)
      (fixedNetwork D ⟨x, z, hxz⟩) :=
  stable_PC D (fixedNetwork D)
    (fixedNetwork_stable D) (fixedNetwork_converse D)
    hxy hyz hxz

end CCO.StrongPC
