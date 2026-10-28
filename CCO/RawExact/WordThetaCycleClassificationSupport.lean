import CCO.RawExact.WordThetaSource
import CCO.RawExact.WordThetaCycleClassificationPaths

/-!
# Exact underlying support of the actual RAW word theta diagram

The chosen old source-atom labels have precisely the already constructed
private fan graph as support. This is independent of pairwise Helly data:
pairwise compatibility controls label uniqueness, whereas support follows
from existence of a genuine reference atom on each actual graph edge.
-/

universe u v w
namespace CCO.RawExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I] {sort : I → ι}

/-- Every and only actual graph root-spokes are specified in the full diagram. -/
theorem privateFanFull_root_support_iff
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (menus : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) (v : PrivateFanVertex S menus centres)
    (h : privateFanRoot S menus centres ≠ v) :
    (∃ a, (privateFanFullDiagram S H menus centres).edge (privateFanRoot S menus centres) v h = some a) ↔
      privateFanAdjacent S menus centres (privateFanRoot S menus centres) v := by
  cases v with
  | inl v =>
      cases v with
      | none => exact False.elim (h rfl)
      | some c =>
          change (∃ a, privateFanRootSelectedAtom S H menus centres (.inl (some c)) = some a) ↔ _
          have ho : (∃ a, privateFanRootSelectedAtom S H menus centres (.inl (some c)) = some a) ↔
              privateFanRootSelectedAtom S H menus centres (.inl (some c)) ≠ none := by
            cases privateFanRootSelectedAtom S H menus centres (.inl (some c)) <;> simp
          exact ho.trans (privateFanRootSelectedAtom_ne_none_iff S H menus centres _)
  | inr p =>
      change (∃ a, privateFanRootSelectedAtom S H menus centres (.inr p) = some a) ↔ _
      have ho : (∃ a, privateFanRootSelectedAtom S H menus centres (.inr p) = some a) ↔
          privateFanRootSelectedAtom S H menus centres (.inr p) ≠ none := by
        cases privateFanRootSelectedAtom S H menus centres (.inr p) <;> simp
      exact ho.trans (privateFanRootSelectedAtom_ne_none_iff S H menus centres _)

/-- The full finite diagram's literal specified edges equal exactly its private fan graph. -/
theorem privateFanFull_support_iff
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (menus : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) (v w : PrivateFanVertex S menus centres) (h : v ≠ w) :
    (∃ a, (privateFanFullDiagram S H menus centres).edge v w h = some a) ↔
      privateFanAdjacent S menus centres v w := by
  by_cases hv : v = privateFanRoot S menus centres
  · subst v
    exact privateFanFull_root_support_iff S H menus centres w h
  · by_cases hw : w = privateFanRoot S menus centres
    · subst w
      constructor
      · rintro ⟨a, ha⟩
        have hr := ((privateFanFullDiagram S H menus centres).edge_reverse _ _ h a).mp ha
        have hg := (privateFanFull_root_support_iff S H menus centres v h.symm).mp ⟨S.conv a, hr⟩
        exact (privateFanAdjacent_symm S menus centres _ _).mp hg
      · intro hg
        obtain ⟨a, ha⟩ := (privateFanFull_root_support_iff S H menus centres v h.symm).mpr
          ((privateFanAdjacent_symm S menus centres _ _).mp hg)
        exact ⟨S.conv a, ((privateFanFullDiagram S H menus centres).edge_reverse _ _ h.symm a).mp ha⟩
    · rw [privateFanFull_nonroot_edge_eq S H menus centres v w hv hw h]
      exact (privateFanPuncturedDiagram_support_iff S H menus centres v w h).trans
        ⟨fun h => h.2.2, fun hg => ⟨hv, hw, hg⟩⟩

/-- Every actual specified cycle edge is an edge of the underlying private fan. -/
theorem privateFanFull_cycle_adjacent
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (menus : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (C : SimpleCycle (privateFanFullDiagram S H menus centres)) :
    ∀ p, privateFanAdjacent S menus centres (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) := by
  intro p
  exact (privateFanFull_support_iff S H menus centres _ _ (C.next_ne p)).mp (C.specified p)

end CCO.RawExact
