import CCO.SafeReadings.SafeTrace

/-! Finite safe certificates are built by actual one-pair recolourings on
the SAME formal vertices. Every recorded edge and every previously made
safe unordered pair is preserved. No equivariant certificate is claimed. -/
universe u v w z
namespace CCO.SafeReadings
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {safe : ∀ i j, S.Menu i j} (hs : SafeSystem S safe)
variable {V : Type z} (D : PartialDiagram S V)

/-- A missing constraint is missing in both orientations. -/
theorem missing_reverse (x y : V) (hxy : x ≠ y) (h : D.edge x y hxy = none) :
    D.edge y x hxy.symm = none := by
  cases he : D.edge y x hxy.symm with
  | none => rfl
  | some a =>
    have hr := (D.edge_reverse y x hxy.symm a).mp he
    rw [h] at hr
    cases hr

/-- The typed point family has a safe actual edge at this ordered pair. -/
def SafeAt (f : DiagramHom D) (x y : V) : Prop :=
  ∃ a ∈ safe (D.vertexSort x) (D.vertexSort y), S.colour (f.point x) (f.point y) = some a

include hs in
 theorem safeAt_reverse (f : DiagramHom D) (x y : V)
    (h : SafeAt S (safe := safe) D f x y) : SafeAt S (safe := safe) D f y x := by
  obtain ⟨a,ha,hcol⟩ := h
  refine ⟨S.conv a, ?_, (S.colour_swap _ _ a).mp hcol⟩
  rw [← hs.opposite]
  exact S.mem_opposite ha

include hs in
/-- Recolouring a missing pair gives another injective realization of
ALL recorded constraints; every other ordered pair keeps its actual colour. -/
theorem recolour_missing_pair (f : DiagramHom D) (hf : f.IsInjective)
    (x y : V) (hxy : x ≠ y) (hmissing : D.edge x y hxy = none) :
    ∃ g : DiagramHom D, g.IsInjective ∧ SafeAt S (safe := safe) D g x y ∧
      (∀ p q, ¬ (p = x ∧ q = y) → ¬ (p = y ∧ q = x) →
        S.colour (g.point p) (g.point q) = S.colour (f.point p) (f.point q)) := by
  let : Finite V := D.finite_type
  obtain ⟨g,hg,hkeep,hgsafe⟩ := one_edge_safe_recolour_typed S hs.amalgamation
    D.vertexSort f.point hf x y hxy
  have hmissing' := missing_reverse S D x y hxy hmissing
  let G : DiagramHom D := {
    point := g
    preserves_edge := by
      intro p q hpq a hrec
      have h1 : ¬ (p = x ∧ q = y) := by
        rintro ⟨rfl,rfl⟩
        rw [hmissing] at hrec
        cases hrec
      have h2 : ¬ (p = y ∧ q = x) := by
        rintro ⟨rfl,rfl⟩
        rw [hmissing'] at hrec
        cases hrec
      exact (hkeep p q h1 h2).trans (f.preserves_edge p q hpq a hrec) }
  exact ⟨G,hg,hgsafe,hkeep⟩

include hs in
/-- Recolour a finite list of requested holes; unordered-pair safety persists
because the given safe system is closed under literal typed converse. -/
theorem safe_certificate_on (f : DiagramHom D) (hf : f.IsInjective)
    (pairs : Finset (V × V)) :
    ∃ g : DiagramHom D, g.IsInjective ∧
      ∀ p ∈ pairs, ∀ h : p.1 ≠ p.2, D.edge p.1 p.2 h = none →
        SafeAt S (safe := safe) D g p.1 p.2 := by
  classical
  induction pairs using Finset.induction_on with
  | empty => exact ⟨f,hf,by simp⟩
  | @insert p pairs hp ih =>
    obtain ⟨g,hg,hgsafe⟩ := ih
    rcases p with ⟨x,y⟩
    by_cases hxy : x ≠ y
    · by_cases hmissing : D.edge x y hxy = none
      · obtain ⟨k,hk,hksafe,hkeep⟩ := recolour_missing_pair S hs D g hg x y hxy hmissing
        refine ⟨k,hk,?_⟩
        rintro ⟨p,q⟩ hpq hneq hnone
        rcases Finset.mem_insert.mp hpq with he | hm
        · cases he
          exact hksafe
        · by_cases h1 : p = x ∧ q = y
          · rcases h1 with ⟨rfl,rfl⟩
            exact hksafe
          · by_cases h2 : p = y ∧ q = x
            · rcases h2 with ⟨rfl,rfl⟩
              exact safeAt_reverse S hs D k _ _ hksafe
            · obtain ⟨a,ha,hcol⟩ := hgsafe (p,q) hm hneq hnone
              exact ⟨a,ha,(hkeep p q h1 h2).trans hcol⟩
      · refine ⟨g,hg,?_⟩
        intro p hp hneq hnone
        rcases Finset.mem_insert.mp hp with he | hm
        · cases he
          exact False.elim (hmissing hnone)
        · exact hgsafe p hm hneq hnone
    · refine ⟨g,hg,?_⟩
      intro p hp hneq hnone
      rcases Finset.mem_insert.mp hp with he | hm
      · cases he
        exact False.elim (hxy hneq)
      · exact hgsafe p hm hneq hnone

include hs in
/-- Every finite injectively completable diagram has an injective safe
certificate on ALL unspecified pairs, including diagrams with ≤2 vertices. -/
theorem safe_certificate (f : DiagramHom D) (hf : f.IsInjective) :
    ∃ g : DiagramHom D, g.IsInjective ∧
      ∀ x y (hxy : x ≠ y), D.edge x y hxy = none →
        ∃ a ∈ safe (D.vertexSort x) (D.vertexSort y), S.colour (g.point x) (g.point y) = some a := by
  classical
  let : Finite V := D.finite_type
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨g,hg,hgsafe⟩ := safe_certificate_on S hs D f hf Finset.univ
  exact ⟨g,hg,fun x y hxy he => hgsafe (x,y) (Finset.mem_univ _) hxy he⟩

end CCO.SafeReadings
