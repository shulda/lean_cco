import CCO.UnaryFreshFrames.ClosureActions

/-! B039 C04–C06: actual SAME-subgroup fresh frames and closed-base orbit
infinitude. The reverse construction uses ONE avoidance element for the whole
finite surplus closure. Neither direction assumes homogeneity or SAP. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

def RealGenerating (R : Set V) : Prop :=
  ∀ x, ∃ r ∈ R, x ∈ H.closureAt r

def FreshFrames (R : Set V) : Prop :=
  ∀ A B : Set V, A.Finite → B.Finite → H.Closed A → H.Closed B → A ⊆ B →
    ∃ D : Set V, D.Finite ∧ D ⊆ R ∧ A ⊆ H.closure D ∧ H.closure D ∩ B = A

def InvariantReal (G : Subgroup H.Aut) (R : Set V) : Prop :=
  ∀ g : G, ∀ x ∈ R, g • x ∈ R

def RealBaseOrbits (G : Subgroup H.Aut) (R : Set V) : Prop :=
  ∀ D : Set V, D.Finite → D ⊆ R → ∀ x, x ∉ H.closure D →
    (orbitOver G D x).Infinite

theorem finite_real_cover {R : Set V} (hR : H.RealGenerating R)
    {A : Set V} (hA : A.Finite) :
    ∃ D : Set V, D.Finite ∧ D ⊆ R ∧ A ⊆ H.closure D := by
  classical
  let rep : V → V := fun x => (hR x).choose
  have hr (x : V) : rep x ∈ R ∧ x ∈ H.closureAt (rep x) := (hR x).choose_spec
  refine ⟨rep '' A, hA.image rep, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (hr x).1
  · intro x hx
    apply H.closure_mono (B := rep '' A) _ (hr x).2
    intro y hy
    have he : y = rep x := hy
    exact ⟨x, hx, he.symm⟩

theorem infiniteClosedOrbits_of_frames (G : Subgroup H.Aut) (hfin : H.LocallyFinite)
    {R : Set V} (hFrames : H.FreshFrames R) (hReal : H.RealBaseOrbits G R) :
    H.InfiniteClosedOrbits G := by
  intro A hA hAc u hu
  let B := H.closure (A ∪ {u})
  have hAB : A ⊆ B := fun x hx => H.subset_closure _ (Or.inl hx)
  have huB : u ∈ B := H.subset_closure _ (Or.inr rfl)
  obtain ⟨D, hD, hDR, hDA, hDB⟩ := hFrames A B hA
    (hfin _ (hA.union (Set.finite_singleton u))) hAc (H.closure_closed _) hAB
  have huD : u ∉ H.closure D := by
    intro h
    apply hu
    rw [← hDB]
    exact ⟨h, huB⟩
  apply (hReal D hD hDR u huD).mono
  rintro y ⟨g, rfl⟩
  refine ⟨⟨g.val, ?_⟩, rfl⟩
  intro a ha
  exact H.closure_fixed g.val.val g.property a (hDA ha)

theorem frames_of_infiniteClosedOrbits (G : Subgroup H.Aut) (hfin : H.LocallyFinite)
    {R : Set V} (hGen : H.RealGenerating R) (hInv : H.InvariantReal G R)
    (hInf : H.InfiniteClosedOrbits G) : H.FreshFrames R := by
  classical
  intro A B hA hB hAc _ hAB
  obtain ⟨D₀, hD₀, hReal, hCover⟩ := H.finite_real_cover hGen hA
  have hS : (H.closure D₀ \ A).Finite := (hfin D₀ hD₀).sdiff
  let moving := hS.toFinset
  let forbidden := hB.toFinset
  have hOrbit (x : V) (hx : x ∈ moving) :
      (MulAction.orbit (fixer G A) x).Infinite :=
    hInf A hA hAc x (hS.mem_toFinset.mp hx).2
  obtain ⟨g, hg⟩ := AclOwners.finite_action_avoidance moving forbidden hOrbit
  let moved : V → V := fun x => g.val • x
  have heq : H.closure (moved '' D₀) = moved '' H.closure D₀ :=
    H.aut_closure g.val.val D₀
  refine ⟨moved '' D₀, hD₀.image moved, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hInv g.val x (hReal hx)
  · intro a ha
    rw [heq]
    exact ⟨a, hCover ha, g.property a ha⟩
  · apply Set.Subset.antisymm
    · rintro y ⟨hy, hyB⟩
      rw [heq] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      by_cases hxA : x ∈ A
      · exact ((g.property x hxA).symm.trans hxy) ▸ hxA
      · exact False.elim (hg x (hS.mem_toFinset.mpr ⟨hx, hxA⟩)
          y (hB.mem_toFinset.mpr hyB) hxy)
    · intro a ha
      refine ⟨?_, hAB ha⟩
      rw [heq]
      exact ⟨a, hCover ha, g.property a ha⟩

theorem fresh_frames_iff (G : Subgroup H.Aut) (hfin : H.LocallyFinite)
    {R : Set V} (hGen : H.RealGenerating R) (hInv : H.InvariantReal G R)
    (hReal : H.RealBaseOrbits G R) :
    H.FreshFrames R ↔ H.InfiniteClosedOrbits G :=
  ⟨fun hf => H.infiniteClosedOrbits_of_frames G hfin hf hReal,
    H.frames_of_infiniteClosedOrbits G hfin hGen hInv⟩

/-- Named unions of real sorts automatically have the actual invariance used
above. No arbitrary subgroup orbit statement is inferred from full-Aut SAP. -/
def realSet (real : L.Sorts → Prop) : Set V := {x | real (H.sort x)}

theorem realSet_invariant (G : Subgroup H.Aut) (real : L.Sorts → Prop) :
    H.InvariantReal G (H.realSet real) := by
  intro g x hx
  change real (H.sort (g • x))
  have hs : H.sort (g • x) = H.sort x := H.aut_sort g.val x
  exact hs.symm ▸ hx

end CCO.UnaryFreshFrames.Structure
