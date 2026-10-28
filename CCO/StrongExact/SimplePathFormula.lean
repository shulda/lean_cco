import CCO.StrongExact.PairSurvivorCompletion
import CCO.StrongExact.FinLinePath
import CCO.StrongExact.CycleIndexReverse
import Lean.Elab.Tactic.Omega

/-!
# The actual simple-path bound in the original STRONG PC source

The quantified paths below have a proved nodup list of ALL formal
vertices. This is distinct from the earlier endpoint-separated-walk bound.
-/

universe u v w z
namespace CCO.StrongPC
variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

/-- Exactly the source's intersection over genuine positive specified
simple paths, with empty family equal to the typed diversity Top. -/
def simplePathBound (x y : V) : S.Menu (D.vertexSort x) (D.vertexSort y) :=
  {a | ∀ p : SimpleSpecifiedPath D x y,
    a ∈ PositiveWord.profile S p.val.word}

/-- Existing stable path propagation applies to every genuinely simple
path as well, without identifying the two quantified path families. -/
theorem fixedNetwork_subset_simplePathBound {x y : V} (hxy : x ≠ y) :
    fixedNetwork D ⟨x,y,hxy⟩ ⊆ simplePathBound D x y := by
  intro a ha p
  exact fixedNetwork_subset_path_profile D p.val ha

/-- A one-edge specified path is genuinely simple, so its singleton
profile forces an atom of the complete simple-path bound to agree with
any pre-existing old fine edge. -/
theorem simplePathBound_compatible (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : a ∈ simplePathBound D x y) :
    ∀ b, D.edge x y hxy = some b → a = b := by
  intro b hb
  let p : SimpleSpecifiedPath D x y :=
    ⟨SpecifiedPath.edge hxy b hb,by simp [SpecifiedPath.vertexList,hxy]⟩
  have h := ha p
  change a ∈ ({b} : S.Menu _ _) at h
  exact h

/-- Any actual whole-diagram survivor belongs to the genuine simple-path
bound. This direction reuses C10 survivor induction and C11 propagation. -/
theorem survivor_subset_simplePathBound {x y : V} (hxy : x ≠ y) :
    D.survivor x y hxy ⊆ simplePathBound D x y := by
  intro a ha
  exact fixedNetwork_subset_simplePathBound D hxy
    (D.survivorNetwork_refines_fixedNetwork ⟨x,y,hxy⟩ ha)

private def formulaLast {E : PartialDiagram S V} (C : SimpleCycle E) : Fin C.length :=
  ⟨C.length - 1,by have hPos := C.length_pos; omega⟩

private def formulaPairOld (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y)) (p q : V) : Prop :=
  ∀ (hpq : p ≠ q) (b : S.Atom (D.vertexSort p) (D.vertexSort q)),
    (D.withPair x y hxy a).edge p q hpq = some b → D.edge p q hpq = some b

private def formulaPairReadout {n : Nat} (vertices : Fin (n + 2) ↪ V)
    (point : ∀ p : Fin (n + 2), X (D.vertexSort (vertices p)))
    (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (p q : Fin (n + 2)) : Prop :=
  ∀ (hne : vertices p ≠ vertices q)
    (b : S.Atom (D.vertexSort (vertices p)) (D.vertexSort (vertices q))),
    (D.withPair x y hxy a).edge (vertices p) (vertices q) hne = some b →
      S.colour (point p) (point q) = some b

private theorem simpleBound_cycleHom_of_old_line
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : a ∈ simplePathBound D x y)
    (C : SimpleCycle (D.withPair x y hxy a))
    (hFirst : C.vertices ⟨0,C.length_pos⟩ = x)
    (hLast : C.vertices (formulaLast C) = y)
    (hOld : ∀ p : Fin C.length, p.val + 1 < C.length →
      formulaPairOld D x y hxy a (C.vertices p) (C.vertices (cyclicNext C.length_pos p))) :
    CycleHom C := by
  classical
  rcases C with ⟨length,hThree,hPos,vertices,nextNe,specified⟩
  cases length with
  | zero => omega
  | succ k =>
      cases k with
      | zero => omega
      | succ n =>
          change vertices (0 : Fin (n + 2)) = x at hFirst
          change vertices (Fin.last (n + 1)) = y at hLast
          subst x
          subst y
          change (∃ point : ∀ p : Fin (n + 2), X (D.vertexSort (vertices p)),
            ∀ (p : Fin (n + 2))
              (b : S.Atom (D.vertexSort (vertices p))
                (D.vertexSort (vertices (cyclicNext hPos p)))),
              (D.withPair (vertices 0) (vertices (Fin.last (n + 1))) hxy a).edge
                (vertices p) (vertices (cyclicNext hPos p)) (nextNe p) = some b →
                S.colour (point p) (point (cyclicNext hPos p)) = some b)
          have hNextLast : cyclicNext hPos (Fin.last (n + 1)) = 0 := by
            apply Fin.ext
            simp [cyclicNext]
          have hOldAt (q : Fin (n + 1)) :
              formulaPairOld D (vertices 0) (vertices (Fin.last (n + 1))) hxy a
                (vertices q.castSucc) (vertices q.succ) := by
            have hNext : cyclicNext hPos q.castSucc = q.succ := by
              apply Fin.ext
              change (q.val + 1) % (n + 2) = q.val + 1
              apply Nat.mod_eq_of_lt
              have hlt := q.isLt
              omega
            have h := hOld q.castSucc (by
              change q.val + 1 < n + 2
              have hlt := q.isLt
              omega)
            change formulaPairOld D (vertices 0) (vertices (Fin.last (n + 1))) hxy a
              (vertices q.castSucc) (vertices (cyclicNext hPos q.castSucc)) at h
            rw [hNext] at h
            exact h
          have hSpecified (q : Fin (n + 1)) :
              ∃ b : S.Atom (D.vertexSort (vertices q.castSucc)) (D.vertexSort (vertices q.succ)),
                D.edge (vertices q.castSucc) (vertices q.succ)
                  (lineStepPair vertices q).ne = some b := by
            have hNext : cyclicNext hPos q.castSucc = q.succ := by
              apply Fin.ext
              change (q.val + 1) % (n + 2) = q.val + 1
              apply Nat.mod_eq_of_lt
              have hlt := q.isLt
              omega
            have hE : ∀ hne : vertices q.castSucc ≠ vertices (cyclicNext hPos q.castSucc),
                ∃ b, (D.withPair (vertices 0) (vertices (Fin.last (n + 1))) hxy a).edge
                  (vertices q.castSucc) (vertices (cyclicNext hPos q.castSucc)) hne = some b := by
              intro _
              exact specified _
            rw [hNext] at hE
            obtain ⟨b,hb⟩ := hE (lineStepPair vertices q).ne
            exact ⟨b,hOldAt q _ b hb⟩
          let atoms := fun q : Fin (n + 1) => Classical.choose (hSpecified q)
          have hEdges : ∀ q : Fin (n + 1),
              D.edge (vertices q.castSucc) (vertices q.succ)
                (lineStepPair vertices q).ne = some (atoms q) :=
            fun q => Classical.choose_spec (hSpecified q)
          have hProfile : a ∈ PositiveWord.profile S
              (specifiedLinePath D n vertices atoms hEdges).word :=
            ha (simpleSpecifiedLine D n vertices atoms hEdges)
          obtain ⟨point,hLetters,hEndpoint⟩ := specifiedLine_realizable_of_profile
            D H sap n vertices atoms hEdges a hProfile
          have hLineReadout (q : Fin (n + 1)) :
              formulaPairReadout D vertices point
                (vertices 0) (vertices (Fin.last (n + 1))) hxy a q.castSucc q.succ := by
            intro h b hb
            have hbOld := hOldAt q h b hb
            have hAtom : atoms q = b := Option.some.inj ((hEdges q).symm.trans hbOld)
            rw [← hAtom]
            exact hLetters q
          have hClosingReadout : formulaPairReadout D vertices point
              (vertices 0) (vertices (Fin.last (n + 1))) hxy a (Fin.last (n + 1)) 0 := by
            intro h b hb
            have hSpec :=
              ((D.withPair (vertices 0) (vertices (Fin.last (n + 1))) hxy a).edge_reverse
                (vertices 0) (vertices (Fin.last (n + 1))) hxy a).mp
                  (D.withPair_specified (vertices 0) (vertices (Fin.last (n + 1))) hxy a)
            have hAtom : S.conv a = b := Option.some.inj (hSpec.symm.trans hb)
            have hColour := (S.colour_swap (point 0) (point (Fin.last (n + 1))) a).mp hEndpoint
            rw [hAtom] at hColour
            exact hColour
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
            let readPair : Fin (n + 2) → Fin (n + 2) → Prop :=
              formulaPairReadout D vertices point (vertices 0)
                (vertices (Fin.last (n + 1))) hxy a
            have hRead : readPair (Fin.last (n + 1)) 0 := hClosingReadout
            rw [← hNextLast,← hpLast] at hRead
            exact hRead (nextNe p) b hb

private theorem formulaNextLast {E : PartialDiagram S V} (C : SimpleCycle E) :
    cyclicNext C.length_pos (formulaLast C) = ⟨0,C.length_pos⟩ := by
  apply Fin.ext
  change (C.length - 1 + 1) % C.length = 0
  have hLength : C.length - 1 + 1 = C.length := by
    have hPos := C.length_pos
    omega
  rw [hLength,Nat.mod_self]

private theorem formulaOtherPair {E : PartialDiagram S V}
    (C : SimpleCycle E) (x y : V)
    (hLast : C.vertices (formulaLast C) = y)
    (hFirst : C.vertices ⟨0,C.length_pos⟩ = x)
    (p : Fin C.length) (hp : p.val + 1 < C.length) :
    ¬(C.vertices p = x ∧ C.vertices (cyclicNext C.length_pos p) = y) ∧
      ¬(C.vertices p = y ∧ C.vertices (cyclicNext C.length_pos p) = x) := by
  have hImpossible : p ≠ formulaLast C := by
    intro he
    have hv := congrArg Fin.val he
    change p.val = C.length - 1 at hv
    have hPos := C.length_pos
    omega
  constructor
  · intro hPair
    apply hImpossible
    apply C.unordered_edge_unique p (formulaLast C)
    simp only [formulaNextLast,hLast,hFirst]
    exact Or.inr hPair
  · intro hPair
    apply hImpossible
    apply C.unordered_edge_unique p (formulaLast C)
    simp only [formulaNextLast,hLast,hFirst]
    exact Or.inl hPair

private theorem simpleBound_cycleHom_of_directed_pair
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : a ∈ simplePathBound D x y)
    (C : SimpleCycle (D.withPair x y hxy a)) (cut : Fin C.length)
    (hy : C.vertices cut = y)
    (hx : C.vertices (cyclicNext C.length_pos cut) = x) : CycleHom C := by
  let R := C.rotate (cyclicNext C.length_pos cut)
  have hLast : R.vertices (formulaLast R) = y :=
    (C.rotate_after_cut_last cut).trans hy
  have hFirst : R.vertices ⟨0,R.length_pos⟩ = x := by
    exact hx
  apply (C.cycleHom_rotate_iff (cyclicNext C.length_pos cut)).mp
  apply simpleBound_cycleHom_of_old_line D H sap x y hxy a ha R hFirst hLast
  intro p hp hpq b hb
  have hOther := formulaOtherPair R x y hLast hFirst p hp
  rw [D.withPair_edge_of_other x y hxy a _ _ hpq hOther.1 hOther.2] at hb
  exact hb

/-- Every new simple cycle from a bound atom is realized over a GENUINE
old simple path. Cycle reversal handles the opposite traversal direction
without making any assertion about reversing endpoint-separated walks. -/
theorem simplePathBound_augmented_cycles
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,z,w} S)
    (hAll : ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty)
    (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : a ∈ simplePathBound D x y)
    (C : SimpleCycle (D.withPair x y hxy a)) : CycleHom C := by
  classical
  by_cases hNew : ∃ cut : Fin C.length,
      (C.vertices cut = x ∧ C.vertices (cyclicNext C.length_pos cut) = y) ∨
      (C.vertices cut = y ∧ C.vertices (cyclicNext C.length_pos cut) = x)
  · obtain ⟨cut,hCut⟩ := hNew
    rcases hCut with ⟨hx,hy⟩ | ⟨hy,hx⟩
    · apply C.cycleHom_reverse_iff.mp
      have hReverse := C.reverse_edge_endpoints cut
      exact simpleBound_cycleHom_of_directed_pair D H sap x y hxy a ha
        C.reverse (cyclicNext C.length_pos cut).rev
        (hReverse.1.trans hy) (hReverse.2.trans hx)
    · exact simpleBound_cycleHom_of_directed_pair D H sap x y hxy a ha C cut hy hx
  · obtain ⟨f,_⟩ :=
      (strongCompletion_iff_nonempty_fixedNetwork D H sap cco).mpr hAll
    refine ⟨fun p => f.point (C.vertices p),?_⟩
    intro p b hb
    have hForward : ¬(C.vertices p = x ∧ C.vertices (cyclicNext C.length_pos p) = y) :=
      fun h => hNew ⟨p,Or.inl h⟩
    have hReverse : ¬(C.vertices p = y ∧ C.vertices (cyclicNext C.length_pos p) = x) :=
      fun h => hNew ⟨p,Or.inr h⟩
    rw [D.withPair_edge_of_other x y hxy a _ _ (C.next_ne p) hForward hReverse] at hb
    exact f.preserves_edge _ _ (C.next_ne p) b hb

/-- Every atom of the genuine simple-path bound extends to an actual
injective completion of the entire original finite diagram. -/
theorem simplePathBound_extends_to_completion
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,z,w} S)
    (hAll : ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty)
    (x y : V) (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : a ∈ simplePathBound D x y) :
    ∃ f : DiagramHom D, f.IsInjective ∧
      S.colour (f.point x) (f.point y) = some a := by
  obtain ⟨g,hg⟩ :=
    (PartialDiagram.strongCompletion_iff_cycles_of_SAP_CCO H sap cco
      (D.withPair x y hxy a)).mpr
        (simplePathBound_augmented_cycles D H sap cco hAll x y hxy a ha)
  let f := D.forgetPairHom x y hxy a (simplePathBound_compatible D x y hxy a ha) g
  exact ⟨f,hg,g.preserves_edge x y hxy a (D.withPair_specified x y hxy a)⟩

/-- Pinned N06/C12: the actual finite STRONG PC domain is exactly the
intersection of profiles of ALL genuine specified simple paths. -/
theorem fixedNetwork_eq_simplePathBound
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,z,w} S)
    (hAll : ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty)
    (x y : V) (hxy : x ≠ y) :
    fixedNetwork D ⟨x,y,hxy⟩ = simplePathBound D x y := by
  apply Set.Subset.antisymm (fixedNetwork_subset_simplePathBound D hxy)
  intro a ha
  exact D.survivorNetwork_refines_fixedNetwork ⟨x,y,hxy⟩
    (simplePathBound_extends_to_completion D H sap cco hAll x y hxy a ha)

/-- Only AFTER proving the genuine source formula do the earlier
endpoint-separated-walk bounds agree, under the same source hypotheses.
The two quantified path families remain distinct definitions. -/
theorem fixedNetwork_eq_positivePathBound
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,z,w} S)
    (hAll : ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty)
    (x y : V) (hxy : x ≠ y) :
    fixedNetwork D ⟨x,y,hxy⟩ = positivePathBound D x y := by
  apply Set.Subset.antisymm (fixedNetwork_subset_positivePathBound D hxy)
  intro a ha
  rw [fixedNetwork_eq_simplePathBound D H sap cco hAll x y hxy]
  intro p
  exact ha p.val

/-- Boundary: no genuine specified simple path contributes no
restriction; its intersection is the original typed diversity Top. -/
theorem simplePathBound_eq_top_of_no_paths (x y : V)
    (hNo : IsEmpty (SimpleSpecifiedPath D x y)) :
    simplePathBound D x y = (Set.univ : S.Menu (D.vertexSort x) (D.vertexSort y)) := by
  ext a
  constructor
  · intro _
    exact Set.mem_univ a
  · intro _ p
    exact False.elim (hNo.false p)

end CCO.StrongPC
