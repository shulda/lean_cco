import CCO.StrongExact.PCCompletion

/-!
# Add one actual typed diversity edge to an old partial diagram

The vertex carrier and named sorts stay literal. Only the selected pair
and its genuine typed converse are overwritten. A separate compatibility
lemma proves that old edges are retained when the chosen atom agrees with
any pre-existing label; stable initial refinement discharges that premise.
-/

universe u v w z
namespace CCO.PartialDiagram
variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

private def transportAtom {x y p q : V} (hp : p = x) (hq : q = y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y)) :
    S.Atom (D.vertexSort p) (D.vertexSort q) := by
  cases hp
  cases hq
  exact a

noncomputable def pairOverrideEdge (x y : V)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (p q : V) (hpq : p ≠ q) :
    Option (S.Atom (D.vertexSort p) (D.vertexSort q)) := by
  classical
  exact if h : p = x ∧ q = y then
      some (transportAtom D h.1 h.2 a)
    else if h : p = y ∧ q = x then
      some (transportAtom D h.1 h.2 (S.conv a))
    else D.edge p q hpq

private theorem pairOverrideEdge_reverse (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (p q : V) (hpq : p ≠ q)
    (b : S.Atom (D.vertexSort p) (D.vertexSort q)) :
    pairOverrideEdge D x y a p q hpq = some b ↔
      pairOverrideEdge D x y a q p hpq.symm = some (S.conv b) := by
  classical
  by_cases hpx : p = x <;> by_cases hqy : q = y <;>
    by_cases hpy : p = y <;> by_cases hqx : q = x
  all_goals subst_vars
  all_goals simp_all only [pairOverrideEdge, transportAtom, and_self, dite_true,
    and_false, false_and, dite_false, Option.some.injEq,
    ne_eq, not_false_eq_true]
  all_goals first | exact D.edge_reverse _ _ _ _ | skip
  all_goals constructor <;> intro hEq <;>
    simpa only [S.conv_invol] using congrArg (fun c => S.conv c) hEq

/-- The literal finite old diagram with one selected fine pair added. -/
noncomputable def withPair (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y)) : PartialDiagram S V where
  finite_type := D.finite_type
  vertexSort := D.vertexSort
  edge := pairOverrideEdge D x y a
  edge_reverse := pairOverrideEdge_reverse D x y hxy a

theorem withPair_specified (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y)) :
    (D.withPair x y hxy a).edge x y hxy = some a := by
  classical
  simp only [withPair, pairOverrideEdge, and_self, dite_true]
  rfl

/-- A compatible added pair retains every literal old specified edge. -/
theorem withPair_preserves_old (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (hCompatible : ∀ b, D.edge x y hxy = some b → a = b)
    (p q : V) (hpq : p ≠ q)
    (b : S.Atom (D.vertexSort p) (D.vertexSort q))
    (hb : D.edge p q hpq = some b) :
    (D.withPair x y hxy a).edge p q hpq = some b := by
  classical
  by_cases hForward : p = x ∧ q = y
  · rcases hForward with ⟨rfl,rfl⟩
    have hAtom := hCompatible b hb
    subst b
    exact withPair_specified D p q hxy a
  · by_cases hReverse : p = y ∧ q = x
    · rcases hReverse with ⟨rfl,rfl⟩
      have hBack := (D.edge_reverse p q hpq b).mp hb
      have hAtom : a = S.conv b := hCompatible (S.conv b) hBack
      have hNew := (D.withPair q p hxy a).edge_reverse q p hxy a
      have hResult := hNew.mp (withPair_specified D q p hxy a)
      have hConv : S.conv a = b := by rw [hAtom, S.conv_invol]
      dsimp only [withPair] at hResult
      rw [hConv] at hResult
      exact hResult
    · simpa only [withPair, pairOverrideEdge, dite_eq_right hForward,
        dite_eq_right hReverse] using hb

/-- Stable singleton refinement proves compatibility of every surviving
atom with the original fine edge, if that edge was already specified. -/
theorem pair_compatible_of_fixed_survivor (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : a ∈ StrongPC.fixedNetwork D ⟨x,y,hxy⟩) :
    ∀ b, D.edge x y hxy = some b → a = b := by
  intro b hb
  exact StrongPC.fixedNetwork_subset_specified_singleton D hxy b hb ha

/-- Forget the added compatible pair while retaining the actual points. -/
def forgetPairHom (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (hCompatible : ∀ b, D.edge x y hxy = some b → a = b)
    (f : DiagramHom (D.withPair x y hxy a)) : DiagramHom D where
  point := f.point
  preserves_edge := fun p q hpq b hb =>
    f.preserves_edge p q hpq b
      (withPair_preserves_old D x y hxy a hCompatible p q hpq b hb)

/-- Every other ordered pair keeps its exact old optional colour. -/
theorem withPair_edge_of_other (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (p q : V) (hpq : p ≠ q)
    (hForward : ¬(p = x ∧ q = y)) (hReverse : ¬(p = y ∧ q = x)) :
    (D.withPair x y hxy a).edge p q hpq = D.edge p q hpq := by
  classical
  simp only [withPair, pairOverrideEdge, dite_eq_right hForward,
    dite_eq_right hReverse]

/-- Each specified augmented edge is an actual old-network survivor,
including the new pair and its correctly typed converse. -/
theorem withPair_atom_in_fixed (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : a ∈ StrongPC.fixedNetwork D ⟨x,y,hxy⟩)
    (hAll : ∀ p : DistinctPair V, (StrongPC.fixedNetwork D p).Nonempty)
    (p q : V) (hpq : p ≠ q)
    (b : S.Atom (D.vertexSort p) (D.vertexSort q))
    (hb : (D.withPair x y hxy a).edge p q hpq = some b) :
    b ∈ StrongPC.fixedNetwork D ⟨p,q,hpq⟩ := by
  classical
  by_cases hForward : p = x ∧ q = y
  · rcases hForward with ⟨rfl,rfl⟩
    have hSpec := withPair_specified D p q hxy a
    have hAtom : a = b := Option.some.inj (hSpec.symm.trans hb)
    rw [← hAtom]
    exact ha
  · by_cases hReverse : p = y ∧ q = x
    · rcases hReverse with ⟨rfl,rfl⟩
      have hSpec := ((D.withPair q p hxy a).edge_reverse q p hxy a).mp
        (withPair_specified D q p hxy a)
      have hAtom : S.conv a = b := Option.some.inj (hSpec.symm.trans hb)
      rw [← hAtom]
      rw [StrongPC.fixedNetwork_converse D ⟨q,p,hxy⟩]
      exact S.mem_opposite ha
    · rw [withPair_edge_of_other D x y hxy a p q hpq hForward hReverse] at hb
      rw [StrongPC.fixedNetwork_eq_specified_singleton_of_nonempty
        D hpq b hb (hAll ⟨p,q,hpq⟩)]
      exact Set.mem_singleton b

end CCO.PartialDiagram
