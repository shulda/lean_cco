import CCO.StrongExact.PairEdgeExtension
import CCO.StrongExact.CycleEdgeUniqueness
import CCO.StrongExact.Survivors

/-!
# Each fixed STRONG PC atom extends to an actual whole-diagram completion

Add the chosen original fine atom on its formal pair. Every new simple
cycle uses this pair at most once. Rotate it so that pair is the closing
edge; the remaining line is entirely old and stable support realizes it
with the chosen endpoint atom. CCO and SAP finish in the original source.
-/

universe u v w z
namespace CCO.StrongPC
variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

private def pairOld (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y)) (p q : V) : Prop :=
  ∀ (hpq : p ≠ q) (b : S.Atom (D.vertexSort p) (D.vertexSort q)),
    (D.withPair x y hxy a).edge p q hpq = some b → D.edge p q hpq = some b

private def pairReadout {n : Nat} (vertices : Fin (n + 2) ↪ V)
    (point : ∀ p : Fin (n + 2), X (D.vertexSort (vertices p)))
    (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (p q : Fin (n + 2)) : Prop :=
  ∀ (hne : vertices p ≠ vertices q)
    (b : S.Atom (D.vertexSort (vertices p)) (D.vertexSort (vertices q))),
    (D.withPair x y hxy a).edge (vertices p) (vertices q) hne = some b →
      S.colour (point p) (point q) = some b

private def augmentedSpecified (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y)) (p q : V) : Prop :=
  ∀ hpq : p ≠ q, ∃ b : S.Atom (D.vertexSort p) (D.vertexSort q),
    (D.withPair x y hxy a).edge p q hpq = some b

private theorem cycleHom_withPair_of_old_line
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (hAll : ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty)
    (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : a ∈ fixedNetwork D ⟨x,y,hxy⟩)
    (C : SimpleCycle (D.withPair x y hxy a))
    (hOld : ∀ p : Fin C.length, p.val + 1 < C.length →
      pairOld D x y hxy a (C.vertices p) (C.vertices (cyclicNext C.length_pos p))) :
    CycleHom C := by
  rcases C with ⟨length,hThree,hPos,vertices,nextNe,specified⟩
  cases length with
  | zero => omega
  | succ k =>
      cases k with
      | zero => omega
      | succ n =>
          change (∃ point : ∀ p : Fin (n + 2), X (D.vertexSort (vertices p)),
            ∀ (p : Fin (n + 2))
              (b : S.Atom (D.vertexSort (vertices p))
                (D.vertexSort (vertices (cyclicNext hPos p)))),
              (D.withPair x y hxy a).edge (vertices p)
                (vertices (cyclicNext hPos p)) (nextNe p) = some b →
                S.colour (point p) (point (cyclicNext hPos p)) = some b)
          have hNextLast : cyclicNext hPos (Fin.last (n + 1)) = 0 := by
            apply Fin.ext
            simp [cyclicNext]
          have hLastFirst : vertices (Fin.last (n + 1)) ≠ vertices 0 :=
            (lineEndpointPair vertices).ne.symm
          have hSpecified : augmentedSpecified D x y hxy a
              (vertices (Fin.last (n + 1)))
              (vertices (cyclicNext hPos (Fin.last (n + 1)))) := by
            intro _
            exact specified _
          rw [hNextLast] at hSpecified
          obtain ⟨closing,hClosing⟩ := hSpecified hLastFirst
          have hClosingMem := D.withPair_atom_in_fixed x y hxy a ha hAll
            _ _ hLastFirst closing hClosing
          have hMem : S.conv closing ∈ fixedNetwork D (lineEndpointPair vertices) := by
            change S.conv closing ∈ fixedNetwork D
              ⟨vertices 0,vertices (Fin.last (n + 1)),hLastFirst.symm⟩
            have hConv := fixedNetwork_converse D
              ⟨vertices (Fin.last (n + 1)),vertices 0,hLastFirst⟩
            change fixedNetwork D ⟨vertices 0,vertices (Fin.last (n + 1)),hLastFirst.symm⟩ =
              S.opposite (fixedNetwork D ⟨vertices (Fin.last (n + 1)),vertices 0,hLastFirst⟩) at hConv
            rw [hConv]
            exact S.mem_opposite hClosingMem
          obtain ⟨point,hEdges,hEndpoint⟩ := stable_line_realizable D H
            (fixedNetwork D) (fixedNetwork_stable D) n vertices (S.conv closing) hMem
          have hLineReadout (q : Fin (n + 1)) :
              pairReadout D vertices point x y hxy a q.castSucc q.succ := by
            intro h b hb
            have hNext : cyclicNext hPos q.castSucc = q.succ := by
              apply Fin.ext
              change (q.val + 1) % (n + 2) = q.val + 1
              apply Nat.mod_eq_of_lt
              have hlt := q.isLt
              omega
            have hOldAt := hOld q.castSucc (by
              change q.val + 1 < n + 2
              have hlt := q.isLt
              omega)
            change pairOld D x y hxy a (vertices q.castSucc)
              (vertices (cyclicNext hPos q.castSucc)) at hOldAt
            rw [hNext] at hOldAt
            have hbOld := hOldAt h b hb
            obtain ⟨c,hc,hColour⟩ := hEdges q
            have hcInitial := fixedNetwork_refines_initial D (lineStepPair vertices q) hc
            change c ∈ initial D ⟨vertices q.castSucc,vertices q.succ,h⟩ at hcInitial
            simp only [initial] at hcInitial
            rw [hbOld] at hcInitial
            have hAtom : c = b := hcInitial
            rw [hAtom] at hColour
            exact hColour
          have hClosingReadout : pairReadout D vertices point x y hxy a
              (Fin.last (n + 1)) 0 := by
            intro h b hb
            have hAtom : closing = b := Option.some.inj (hClosing.symm.trans hb)
            have hColour := (S.colour_swap (point 0) (point (Fin.last (n + 1)))
              (S.conv closing)).mp hEndpoint
            simpa only [S.conv_invol,hAtom] using hColour
          refine ⟨point,?_⟩
          intro p b hb
          by_cases hp : p.val + 1 < n + 2
          · let q : Fin (n + 1) := ⟨p.val,by omega⟩
            have hSource : q.castSucc = p := Fin.ext rfl
            have hTarget : q.succ = cyclicNext hPos p := by
              apply Fin.ext
              change p.val + 1 = (p.val + 1) % (n + 2)
              exact (Nat.mod_eq_of_lt hp).symm
            have hRead := hLineReadout q
            rw [hSource,hTarget] at hRead
            exact hRead (nextNe p) b hb
          · have hpLast : p = Fin.last (n + 1) := by
              apply Fin.ext
              simp only [Fin.val_last]
              have hlt := p.isLt
              omega
            have hRead := hClosingReadout
            rw [← hNextLast,← hpLast] at hRead
            exact hRead (nextNe p) b hb

private def cycleLast {E : PartialDiagram S V} (C : SimpleCycle E) : Fin C.length :=
  ⟨C.length - 1,by have hPos := C.length_pos; omega⟩

private theorem cycleNextLast {E : PartialDiagram S V} (C : SimpleCycle E) :
    cyclicNext C.length_pos (cycleLast C) = ⟨0,C.length_pos⟩ := by
  apply Fin.ext
  change (C.length - 1 + 1) % C.length = 0
  have hLength : C.length - 1 + 1 = C.length := by
    have hPos := C.length_pos
    omega
  rw [hLength,Nat.mod_self]

private theorem other_line_pair {E : PartialDiagram S V}
    (C : SimpleCycle E) (x y : V)
    (hClosing : (C.vertices (cycleLast C) = x ∧ C.vertices ⟨0,C.length_pos⟩ = y) ∨
      (C.vertices (cycleLast C) = y ∧ C.vertices ⟨0,C.length_pos⟩ = x))
    (p : Fin C.length) (hp : p.val + 1 < C.length) :
    ¬(C.vertices p = x ∧ C.vertices (cyclicNext C.length_pos p) = y) ∧
      ¬(C.vertices p = y ∧ C.vertices (cyclicNext C.length_pos p) = x) := by
  have hImpossible : p ≠ cycleLast C := by
    intro he
    have hv := congrArg Fin.val he
    change p.val = C.length - 1 at hv
    have hPos := C.length_pos
    omega
  constructor
  · intro hPair
    apply hImpossible
    apply C.unordered_edge_unique p (cycleLast C)
    rcases hClosing with ⟨hLast,hZero⟩ | ⟨hLast,hZero⟩
    · simp only [cycleNextLast,hLast,hZero]
      exact Or.inl hPair
    · simp only [cycleNextLast,hLast,hZero]
      exact Or.inr hPair
  · intro hPair
    apply hImpossible
    apply C.unordered_edge_unique p (cycleLast C)
    rcases hClosing with ⟨hLast,hZero⟩ | ⟨hLast,hZero⟩
    · simp only [cycleNextLast,hLast,hZero]
      exact Or.inr hPair
    · simp only [cycleNextLast,hLast,hZero]
      exact Or.inl hPair

/-- Every simple cycle of the single-edge augmented diagram has an
actual original-colour homomorphism. The chosen edge is rotated to the
closing position; unordered-edge uniqueness proves all other steps old. -/
theorem fixed_survivor_augmented_cycles
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (hAll : ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty)
    (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : a ∈ fixedNetwork D ⟨x,y,hxy⟩)
    (C : SimpleCycle (D.withPair x y hxy a)) : CycleHom C := by
  classical
  by_cases hNew : ∃ cut : Fin C.length,
      (C.vertices cut = x ∧ C.vertices (cyclicNext C.length_pos cut) = y) ∨
      (C.vertices cut = y ∧ C.vertices (cyclicNext C.length_pos cut) = x)
  · obtain ⟨cut,hCut⟩ := hNew
    let R := C.rotate (cyclicNext C.length_pos cut)
    have hLast : R.vertices (cycleLast R) = C.vertices cut := by
      exact C.rotate_after_cut_last cut
    have hZero : R.vertices ⟨0,R.length_pos⟩ =
        C.vertices (cyclicNext C.length_pos cut) := rfl
    have hClosing : (R.vertices (cycleLast R) = x ∧ R.vertices ⟨0,R.length_pos⟩ = y) ∨
        (R.vertices (cycleLast R) = y ∧ R.vertices ⟨0,R.length_pos⟩ = x) := by
      rcases hCut with ⟨hx,hy⟩ | ⟨hy,hx⟩
      · exact Or.inl ⟨hLast.trans hx,hZero.trans hy⟩
      · exact Or.inr ⟨hLast.trans hy,hZero.trans hx⟩
    apply (C.cycleHom_rotate_iff (cyclicNext C.length_pos cut)).mp
    apply cycleHom_withPair_of_old_line D H hAll x y hxy a ha R
    intro p hp hpq b hb
    have hOther := other_line_pair R x y hClosing p hp
    rw [D.withPair_edge_of_other x y hxy a _ _ hpq hOther.1 hOther.2] at hb
    exact hb
  · apply cycleHom_withPair_of_old_line D H hAll x y hxy a ha C
    intro p _hp hpq b hb
    have hForward : ¬(C.vertices p = x ∧ C.vertices (cyclicNext C.length_pos p) = y) :=
      fun h => hNew ⟨p,Or.inl h⟩
    have hReverse : ¬(C.vertices p = y ∧ C.vertices (cyclicNext C.length_pos p) = x) :=
      fun h => hNew ⟨p,Or.inr h⟩
    rw [D.withPair_edge_of_other x y hxy a _ _ hpq hForward hReverse] at hb
    exact hb

/-- Every selected fixed-network atom extends to an actual injective
completion of the whole old diagram, in the original SAP+CCO source. -/
theorem fixed_atom_extends_to_completion
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,z,w} S)
    (hAll : ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty)
    (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : a ∈ fixedNetwork D ⟨x,y,hxy⟩) :
    ∃ f : DiagramHom D, f.IsInjective ∧
      S.colour (f.point x) (f.point y) = some a := by
  obtain ⟨g,hg⟩ :=
    (PartialDiagram.strongCompletion_iff_cycles_of_SAP_CCO H sap cco
      (D.withPair x y hxy a)).mpr
        (fixed_survivor_augmented_cycles D H hAll x y hxy a ha)
  let f := D.forgetPairHom x y hxy a
    (D.pair_compatible_of_fixed_survivor x y hxy a ha) g
  refine ⟨f,hg,?_⟩
  exact g.preserves_edge x y hxy a (D.withPair_specified x y hxy a)

/-- The actual PC domain equals precisely the whole-diagram survivor
menu, with every survivor witnessed by its own injective completion. -/
theorem fixedNetwork_eq_survivor
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,z,w} S)
    (hAll : ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty)
    (x y : V) (hxy : x ≠ y) :
    fixedNetwork D ⟨x,y,hxy⟩ = D.survivor x y hxy := by
  apply Set.Subset.antisymm
  · intro a ha
    exact fixed_atom_extends_to_completion D H sap cco hAll x y hxy a ha
  · exact D.survivorNetwork_refines_fixedNetwork ⟨x,y,hxy⟩

end CCO.StrongPC
