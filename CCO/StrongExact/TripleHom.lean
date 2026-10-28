import CCO.StrongExact.TripleDiagram
import CCO.StrongExact.PrescribedPairCompletion

/-! Different supported real root triangles realize the SAME C09 word diagram. -/

universe u v w
namespace CCO.StrongExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j k : ι}

theorem tripleWordAdjacent_endpoints (W : TripleWords S i j k)
    {x y : tripleVertices S W} (h : tripleWordAdjacent S W x y) :
    ∃ (s : TripleSide) (b : Fin (TripleWords.side S W s).length)
      (e : wordEdgeIndex S ((TripleWords.side S W s).get b)),
      (x = tripleBranchSource S W s b e ∧ y = tripleBranchTarget S W s b e) ∨
      (x = tripleBranchTarget S W s b e ∧ y = tripleBranchSource S W s b e) := by
  obtain ⟨s,a,b,hAdj,ha,hb⟩ := h
  obtain ⟨arc,hArc,hSrc,hDst⟩ := hAdj
  obtain ⟨d,e,hForward | hReverse⟩ :=
    thetaArc_endpoints_on_branch S (TripleWords.side S W s) arc hArc
  · exact ⟨s,d,e,Or.inl
      ⟨ha.symm.trans (congrArg (thetaIntoTriple S W s) (hSrc.symm.trans hForward.1)),
       hb.symm.trans (congrArg (thetaIntoTriple S W s) (hDst.symm.trans hForward.2))⟩⟩
  · exact ⟨s,d,e,Or.inr
      ⟨ha.symm.trans (congrArg (thetaIntoTriple S W s) (hSrc.symm.trans hReverse.1)),
       hb.symm.trans (congrArg (thetaIntoTriple S W s) (hDst.symm.trans hReverse.2))⟩⟩

private def triplePairPreserves {W : TripleWords S i j k}
    (D : PartialDiagram S (tripleVertices S W))
    (point : ∀ x : tripleVertices S W, X (D.vertexSort x))
    (x y : tripleVertices S W) : Prop :=
  ∀ (hxy : x ≠ y) (a : S.Atom (D.vertexSort x) (D.vertexSort y)),
    D.edge x y hxy = some a → S.colour (point x) (point y) = some a

private theorem triplePairPreserves_reverse {W : TripleWords S i j k}
    (D : PartialDiagram S (tripleVertices S W))
    (point : ∀ x : tripleVertices S W, X (D.vertexSort x))
    {x y : tripleVertices S W} (h : triplePairPreserves S D point x y) :
    triplePairPreserves S D point y x := by
  intro hyx a ha
  exact (S.colour_swap (point y) (point x) a).mpr
    (h hyx.symm (S.conv a) ((D.edge_reverse y x hyx a).mp ha))

/-- Alternative root-triangle line witnesses preserve every old edge
of the original fixed seed diagram. No diagram is changed for a new atom. -/
noncomputable def tripleHomBetweenLines (W : TripleWords S i j k)
    (x : X i) (y : X j) (z : X k) (seed : TripleLiteralLines S W x y z)
    (x' : X i) (y' : X j) (z' : X k) (lines : TripleLiteralLines S W x' y' z') :
    DiagramHom (tripleDiagram S W x y z seed) where
  point := tripleLinePoint S W x' y' z' lines
  preserves_edge := by
    classical
    intro a b hab c hc
    let point := tripleLinePoint S W x' y' z' lines
    have hBranch : ∀ (s : TripleSide) (d : Fin (TripleWords.side S W s).length)
        (e : wordEdgeIndex S ((TripleWords.side S W s).get d)),
        triplePairPreserves S (tripleDiagram S W x y z seed) point
          (tripleBranchSource S W s d e) (tripleBranchTarget S W s d e) := by
      intro s d e hne old hOld
      have hForward := tripleDiagram_forward S W x y z seed s d e
      have hAtom : old = tripleBranchAtom S W s d e :=
        Option.some.inj (hOld.symm.trans hForward)
      subst old
      exact tripleLinePoint_letter S W x' y' z' lines s d e
    have hAdj : tripleWordAdjacent S W a b := by
      change (if tripleWordAdjacent S W a b then S.colour _ _ else none) = some c at hc
      by_contra hNo
      simp [hNo] at hc
    obtain ⟨s,d,e,hForward | hReverse⟩ := tripleWordAdjacent_endpoints S W hAdj
    · have hPair : triplePairPreserves S (tripleDiagram S W x y z seed) point a b := by
        rw [hForward.1,hForward.2]
        exact hBranch s d e
      exact hPair hab c hc
    · have hPair : triplePairPreserves S (tripleDiagram S W x y z seed) point a b := by
        rw [hReverse.1,hReverse.2]
        exact triplePairPreserves_reverse S (tripleDiagram S W x y z seed) point
          (hBranch s d e)
      exact hPair hab c hc

/-- Literal lines for all three side presentations, obtained from their
actual atom memberships over one fixed old-colour root triangle. -/
noncomputable def TripleLiteralLines.of_membership
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S) (W : TripleWords S i j k)
    (a : S.Atom i j) (b : S.Atom j k) (c : S.Atom i k)
    (ha : a ∈ present S W.left) (hb : b ∈ present S W.right)
    (hc : c ∈ present S W.across)
    (x : X i) (y : X j) (z : X k)
    (hxy : S.colour x y = some a) (hyz : S.colour y z = some b)
    (hxz : S.colour x z = some c) : TripleLiteralLines S W x y z where
  left d := LiteralLine.of_represented S (W.left.get d) x y
    (profile_realizes_prescribed_pair_of_SAP S H sap (W.left.get d) a
      (ha _ (List.get_mem W.left d)) x y hxy)
  right d := LiteralLine.of_represented S (W.right.get d) y z
    (profile_realizes_prescribed_pair_of_SAP S H sap (W.right.get d) b
      (hb _ (List.get_mem W.right d)) y z hyz)
  across d := LiteralLine.of_represented S (W.across.get d) x z
    (profile_realizes_prescribed_pair_of_SAP S H sap (W.across.get d) c
      (hc _ (List.get_mem W.across d)) x z hxz)

theorem tripleSideRoots_ne (W : TripleWords S i j k) (s : TripleSide) :
    (.inl (tripleSideSource s) : tripleVertices S W) ≠ .inl (tripleSideTarget s) := by
  cases s <;> intro h <;> cases h

/-- Each fixed-diagram survivor respects every positive word on that side. -/
theorem triple_survivor_subset_present
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S) (W : TripleWords S i j k)
    (x : X i) (y : X j) (z : X k) (seed : TripleLiteralLines S W x y z)
    (s : TripleSide) :
    (tripleDiagram S W x y z seed).survivor
      (.inl (tripleSideSource s)) (.inl (tripleSideTarget s))
      (tripleSideRoots_ne S W s) ⊆ present S (TripleWords.side S W s) := by
  rintro a ⟨f,_hf,hColour⟩ word hw
  obtain ⟨d,hd⟩ := List.mem_iff_get.mp hw
  subst word
  exact (positive_profile_iff_represented S H sap _ a).mpr
    ⟨_,_,tripleDiagramHom_represented_side S W x y z seed f s d,hColour⟩

/-- Any original root-triangle line witness yields an injective completion
retaining the chosen pair's actual diversity atom. -/
theorem triple_lines_give_survivor
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S) (W : TripleWords S i j k)
    (x : X i) (y : X j) (z : X k) (seed : TripleLiteralLines S W x y z)
    (x' : X i) (y' : X j) (z' : X k) (lines : TripleLiteralLines S W x' y' z')
    (s : TripleSide)
    (a : S.Atom (tripleRootSort i j k (tripleSideSource s))
      (tripleRootSort i j k (tripleSideTarget s)))
    (ha : S.colour (tripleRootPoint x' y' z' (tripleSideSource s))
      (tripleRootPoint x' y' z' (tripleSideTarget s)) = some a) :
    a ∈ (tripleDiagram S W x y z seed).survivor
      (.inl (tripleSideSource s)) (.inl (tripleSideTarget s))
      (tripleSideRoots_ne S W s) := by
  let f := tripleHomBetweenLines S W x y z seed x' y' z' lines
  obtain ⟨g,hg,hColour⟩ := f.strongCompletion_preserves_pair_of_SAP H sap
    (.inl (tripleSideSource s)) (.inl (tripleSideTarget s)) a ha
  exact ⟨g,hg,hColour⟩

end CCO.StrongExact
