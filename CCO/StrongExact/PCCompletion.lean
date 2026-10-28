import CCO.StrongExact.CycleCutPath
import Lean.Elab.Tactic.Omega

/-!
# Nonempty stable STRONG PC domains give actual source completion

Every genuine SimpleCycle is cut at its closing edge into an injectively
enumerated formal line. The old closing atom survives by nonemptiness and
initial singleton refinement. A stable line witness realizes all remaining
specified edges and that closing atom. Semantic CCO and original SAP then
supply an actual injective whole-diagram completion.
-/

universe u v w z
namespace CCO.StrongPC
variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

private def specifiedPair (x y : V) : Prop :=
  ∃ h : x ≠ y, ∃ a : S.Atom (D.vertexSort x) (D.vertexSort y),
    D.edge x y h = some a

private def linePairPreserves {n : Nat} (vertices : Fin (n + 2) ↪ V)
    (point : ∀ p : Fin (n + 2), X (D.vertexSort (vertices p)))
    (p q : Fin (n + 2)) : Prop :=
  ∀ (h : vertices p ≠ vertices q)
    (a : S.Atom (D.vertexSort (vertices p)) (D.vertexSort (vertices q))),
    D.edge (vertices p) (vertices q) h = some a →
      S.colour (point p) (point q) = some a

/-- All specified simple cycles are homomorphic whenever every domain of
a stable refinement of the initial network is nonempty. -/
theorem stable_cycles_realizable
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (N : Network D) (hStable : Stable D N)
    (hInit : Refines D N (initial D))
    (hNonempty : ∀ p : DistinctPair V, (N p).Nonempty)
    (C : SimpleCycle D) : CycleHom C := by
  rcases C with ⟨length, hThree, hPos, vertices, nextNe, specified⟩
  cases length with
  | zero => omega
  | succ k =>
      cases k with
      | zero => omega
      | succ n =>
          change (∃ point : ∀ p : Fin (n + 2), X (D.vertexSort (vertices p)),
            ∀ (p : Fin (n + 2))
              (a : S.Atom (D.vertexSort (vertices p))
                (D.vertexSort (vertices (cyclicNext hPos p)))),
              D.edge (vertices p) (vertices (cyclicNext hPos p)) (nextNe p) = some a →
                S.colour (point p) (point (cyclicNext hPos p)) = some a)
          change (∀ p : Fin (n + 2), ∃ a : S.Atom (D.vertexSort (vertices p))
            (D.vertexSort (vertices (cyclicNext hPos p))),
            D.edge (vertices p) (vertices (cyclicNext hPos p)) (nextNe p) = some a) at specified
          have hNextLast : cyclicNext hPos (Fin.last (n + 1)) = 0 := by
            apply Fin.ext
            simp [cyclicNext]
          have hLastFirst : vertices (Fin.last (n + 1)) ≠ vertices 0 :=
            (lineEndpointPair vertices).ne.symm
          have hSpecified : specifiedPair D (vertices (Fin.last (n + 1)))
              (vertices (cyclicNext hPos (Fin.last (n + 1)))) :=
            ⟨nextNe _, specified _⟩
          rw [hNextLast] at hSpecified
          obtain ⟨_, closing, hClosing⟩ := hSpecified
          have hReverse : D.edge (vertices 0) (vertices (Fin.last (n + 1)))
              (lineEndpointPair vertices).ne = some (S.conv closing) :=
            (D.edge_reverse _ _ hLastFirst closing).mp hClosing
          have hMem : S.conv closing ∈ N (lineEndpointPair vertices) := by
            obtain ⟨b, hb⟩ := hNonempty (lineEndpointPair vertices)
            have h := hInit (lineEndpointPair vertices) hb
            change b ∈ initial D (lineEndpointPair vertices) at h
            simp only [initial, lineEndpointPair, hReverse] at h
            rw [h] at hb
            exact hb
          obtain ⟨point,hEdges,hEndpoint⟩ :=
            stable_line_realizable D H N hStable n vertices (S.conv closing) hMem
          have hLineReadout (q : Fin (n + 1)) :
              linePairPreserves D vertices point q.castSucc q.succ := by
            intro h a ha
            obtain ⟨b,hb,hColour⟩ := hEdges q
            have hB := hInit (lineStepPair vertices q) hb
            change b ∈ initial D ⟨vertices q.castSucc, vertices q.succ, h⟩ at hB
            simp only [initial] at hB
            rw [ha] at hB
            have hBA : b = a := hB
            rw [hBA] at hColour
            exact hColour
          have hClosingReadout : linePairPreserves D vertices point
              (Fin.last (n + 1)) 0 := by
            intro h a ha
            have hAtom : closing = a := Option.some.inj (hClosing.symm.trans ha)
            have hColour :=
              (S.colour_swap (point 0) (point (Fin.last (n + 1)))
                (S.conv closing)).mp hEndpoint
            simpa only [S.conv_invol, hAtom] using hColour
          refine ⟨point, ?_⟩
          intro p a ha
          by_cases hp : p.val + 1 < n + 2
          · let q : Fin (n + 1) := ⟨p.val, by omega⟩
            have hSource : q.castSucc = p := Fin.ext rfl
            have hTarget : q.succ = cyclicNext hPos p := by
              apply Fin.ext
              change p.val + 1 = (p.val + 1) % (n + 2)
              exact (Nat.mod_eq_of_lt hp).symm
            have hRead := hLineReadout q
            rw [hSource, hTarget] at hRead
            exact hRead (nextNe p) a ha
          · have hpLast : p = Fin.last (n + 1) := by
              apply Fin.ext
              simp only [Fin.val_last]
              have hlt := p.isLt
              omega
            have hRead := hClosingReadout
            rw [← hNextLast, ← hpLast] at hRead
            exact hRead (nextNe p) a ha

/-- This is an actual injective completion, with no assumed completion,
word-Helly or PC-completeness provider hidden in the hypotheses. -/
theorem strongCompletion_of_stable_nonempty
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,z,w} S)
    (N : Network D) (hStable : Stable D N)
    (hInit : Refines D N (initial D))
    (hNonempty : ∀ p : DistinctPair V, (N p).Nonempty) :
    D.HasStrongCompletion :=
  (PartialDiagram.strongCompletion_iff_cycles_of_SAP_CCO H sap cco D).mpr
    (stable_cycles_realizable D H N hStable hInit hNonempty)

/-- The canonical finite STRONG PC fixed point has no empty domain iff
its original finite partial diagram has an injective source completion. -/
theorem strongCompletion_iff_nonempty_fixedNetwork
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,z,w} S) :
    D.HasStrongCompletion ↔
      ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty := by
  constructor
  · rintro ⟨f,hf⟩ p
    exact fixedNetwork_nonempty_of_completion D f hf p
  · intro hNonempty
    exact strongCompletion_of_stable_nonempty D H sap cco
      (fixedNetwork D) (fixedNetwork_stable D)
      (fixedNetwork_refines_initial D) hNonempty

end CCO.StrongPC
