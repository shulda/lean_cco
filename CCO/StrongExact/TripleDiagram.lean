import CCO.StrongExact.TripleWords

/-! The actual C09 three-root private-word diagram and original-letter semantics. -/

universe u v w
namespace CCO.StrongExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j k : ι}

noncomputable def tripleBranchSource (W : TripleWords S i j k) (s : TripleSide)
    (b : Fin (TripleWords.side S W s).length)
    (e : wordEdgeIndex S ((TripleWords.side S W s).get b)) : tripleVertices S W :=
  thetaIntoTriple S W s (thetaBranchEdgeSource S (TripleWords.side S W s) b e)

noncomputable def tripleBranchTarget (W : TripleWords S i j k) (s : TripleSide)
    (b : Fin (TripleWords.side S W s).length)
    (e : wordEdgeIndex S ((TripleWords.side S W s).get b)) : tripleVertices S W :=
  thetaIntoTriple S W s (thetaBranchEdgeTarget S (TripleWords.side S W s) b e)

theorem tripleBranch_distinct (W : TripleWords S i j k) (s : TripleSide)
    (b : Fin (TripleWords.side S W s).length)
    (e : wordEdgeIndex S ((TripleWords.side S W s).get b)) :
    tripleBranchSource S W s b e ≠ tripleBranchTarget S W s b e := by
  intro h
  exact thetaBranchEdge_distinct S (TripleWords.side S W s) b e
    ((thetaIntoTriple_injective S W s) h)

noncomputable def tripleBranchAtom (W : TripleWords S i j k) (s : TripleSide)
    (b : Fin (TripleWords.side S W s).length)
    (e : wordEdgeIndex S ((TripleWords.side S W s).get b)) :
    S.Atom (tripleVertexSort S W (tripleBranchSource S W s b e))
      (tripleVertexSort S W (tripleBranchTarget S W s b e)) :=
  (thetaIntoTriple_sort S W s
    (thetaBranchEdgeSource S (TripleWords.side S W s) b e)).symm ▸
  ((thetaIntoTriple_sort S W s
    (thetaBranchEdgeTarget S (TripleWords.side S W s) b e)).symm ▸
      thetaBranchEdgeAtom S (TripleWords.side S W s) b e)

private theorem triple_cast_of_sigma_eq {s t : ι} (h : s = t)
    (x : X s) (y : X t) (hc : (⟨s,x⟩ : Sigma X) = ⟨t,y⟩) : h ▸ x = y := by
  cases hc
  rfl

private theorem triple_colour_uncast_both {s t s' t' : ι}
    (hs : s = s') (ht : t = t') (a : S.Atom s' t') (x : X s) (y : X t)
    (hxy : S.colour (hs ▸ x) (ht ▸ y) = some a) :
    S.colour x y = some (hs.symm ▸ (ht.symm ▸ a)) := by
  cases hs
  cases ht
  simpa using hxy

/-- Every side letter is read with its actual old original-sort atom. -/
theorem tripleLinePoint_letter (W : TripleWords S i j k)
    (x : X i) (y : X j) (z : X k) (lines : TripleLiteralLines S W x y z)
    (s : TripleSide) (b : Fin (TripleWords.side S W s).length)
    (e : wordEdgeIndex S ((TripleWords.side S W s).get b)) :
    S.colour (tripleLinePoint S W x y z lines (tripleBranchSource S W s b e))
      (tripleLinePoint S W x y z lines (tripleBranchTarget S W s b e)) =
      some (tripleBranchAtom S W s b e) := by
  unfold tripleBranchAtom
  apply triple_colour_uncast_both S
    (thetaIntoTriple_sort S W s
      (thetaBranchEdgeSource S (TripleWords.side S W s) b e))
    (thetaIntoTriple_sort S W s
      (thetaBranchEdgeTarget S (TripleWords.side S W s) b e))
  have hs := triple_cast_of_sigma_eq
    (thetaIntoTriple_sort S W s
      (thetaBranchEdgeSource S (TripleWords.side S W s) b e)) _ _
    (tripleLinePoint_side_image S W x y z lines s
      (thetaBranchEdgeSource S (TripleWords.side S W s) b e))
  have ht := triple_cast_of_sigma_eq
    (thetaIntoTriple_sort S W s
      (thetaBranchEdgeTarget S (TripleWords.side S W s) b e)) _ _
    (tripleLinePoint_side_image S W x y z lines s
      (thetaBranchEdgeTarget S (TripleWords.side S W s) b e))
  dsimp only [tripleBranchSource,tripleBranchTarget]
  rw [hs,ht]
  exact thetaFamilyLinePoint_letter S (TripleWords.side S W s)
    (tripleRootPoint x y z (tripleSideSource s))
    (tripleRootPoint x y z (tripleSideTarget s))
    (TripleLiteralLines.side S lines s) b e

def tripleWordAdjacent (W : TripleWords S i j k) (x y : tripleVertices S W) : Prop :=
  ∃ (s : TripleSide) (a b : thetaVertices S (TripleWords.side S W s)),
    thetaAdjacent S (TripleWords.side S W s) a b ∧
      thetaIntoTriple S W s a = x ∧ thetaIntoTriple S W s b = y

theorem tripleWordAdjacent_symmetric (W : TripleWords S i j k)
    {x y : tripleVertices S W} (h : tripleWordAdjacent S W x y) :
    tripleWordAdjacent S W y x := by
  obtain ⟨s,a,b,hAdj,ha,hb⟩ := h
  exact ⟨s,b,a,thetaAdjacent_symmetric S (TripleWords.side S W s) hAdj,hb,ha⟩

/-- A single original optional colour on each specified formal pair.
Only genuine side-word adjacencies are recorded. -/
noncomputable def tripleDiagram (W : TripleWords S i j k)
    (x : X i) (y : X j) (z : X k) (lines : TripleLiteralLines S W x y z) :
    PartialDiagram S (tripleVertices S W) := by
  classical
  let point := tripleLinePoint S W x y z lines
  refine ⟨finite_tripleVertices S W,tripleVertexSort S W,
    (fun a b _ => if tripleWordAdjacent S W a b then
      S.colour (point a) (point b) else none), ?_⟩
  intro a b hab c
  by_cases hAdj : tripleWordAdjacent S W a b
  · have hRev := tripleWordAdjacent_symmetric S W hAdj
    simp only [ite_eq_left hAdj,ite_eq_left hRev]
    exact S.colour_swap (point a) (point b) c
  · have hRev : ¬ tripleWordAdjacent S W b a := by
      intro h
      exact hAdj (tripleWordAdjacent_symmetric S W h)
    simp [hAdj,hRev]

theorem tripleDiagram_forward (W : TripleWords S i j k)
    (x : X i) (y : X j) (z : X k) (lines : TripleLiteralLines S W x y z)
    (s : TripleSide) (b : Fin (TripleWords.side S W s).length)
    (e : wordEdgeIndex S ((TripleWords.side S W s).get b)) :
    (tripleDiagram S W x y z lines).edge
      (tripleBranchSource S W s b e) (tripleBranchTarget S W s b e)
      (tripleBranch_distinct S W s b e) = some (tripleBranchAtom S W s b e) := by
  classical
  have hAdj : tripleWordAdjacent S W
      (tripleBranchSource S W s b e) (tripleBranchTarget S W s b e) :=
    ⟨s,_,_,thetaAdjacent_forward S (TripleWords.side S W s) b e,rfl,rfl⟩
  change (if tripleWordAdjacent S W _ _ then S.colour _ _ else none) = _
  rw [ite_eq_left hAdj]
  exact tripleLinePoint_letter S W x y z lines s b e

/-- Every diagram homomorphism realizes every original side word over
its corresponding two literal global roots. -/
theorem tripleDiagramHom_represented_side (W : TripleWords S i j k)
    (x : X i) (y : X j) (z : X k) (lines : TripleLiteralLines S W x y z)
    (f : DiagramHom (tripleDiagram S W x y z lines)) (s : TripleSide)
    (b : Fin (TripleWords.side S W s).length) :
    PositiveWord.represented S ((TripleWords.side S W s).get b)
      (f.point (.inl (tripleSideSource s)))
      (f.point (.inl (tripleSideTarget s))) := by
  let sidePoint : ∀ a : thetaVertices S (TripleWords.side S W s),
      X (thetaVertexSort S (TripleWords.side S W s) a) :=
    fun a => (thetaIntoTriple_sort S W s a) ▸ f.point (thetaIntoTriple S W s a)
  let point : ∀ p : wordPositions S ((TripleWords.side S W s).get b),
      X (wordPositionSort S ((TripleWords.side S W s).get b) p) :=
    fun p => (thetaBranchPosition_sort S (TripleWords.side S W s) b p) ▸
      sidePoint (thetaBranchPosition S (TripleWords.side S W s) b p)
  have hLetters : ∀ e : wordEdgeIndex S ((TripleWords.side S W s).get b),
      S.colour (point (wordEdgeSource S _ e)) (point (wordEdgeTarget S _ e)) =
        some (wordEdgeAtom S _ e) := by
    intro e
    have he := f.preserves_edge _ _ (tripleBranch_distinct S W s b e)
      (tripleBranchAtom S W s b e) (tripleDiagram_forward S W x y z lines s b e)
    have hSide := colour_cast_both S
      (thetaIntoTriple_sort S W s
        (thetaBranchEdgeSource S (TripleWords.side S W s) b e))
      (thetaIntoTriple_sort S W s
        (thetaBranchEdgeTarget S (TripleWords.side S W s) b e))
      (thetaBranchEdgeAtom S (TripleWords.side S W s) b e)
      (f.point (tripleBranchSource S W s b e))
      (f.point (tripleBranchTarget S W s b e)) he
    rw [thetaBranchEdgeAtom_cast S (TripleWords.side S W s) b e] at hSide
    exact colour_cast_both S
      (thetaBranchPosition_sort S (TripleWords.side S W s) b (wordEdgeSource S _ e))
      (thetaBranchPosition_sort S (TripleWords.side S W s) b (wordEdgeTarget S _ e))
      (wordEdgeAtom S _ e) _ _ hSide
  have hWord := represented_of_literal_word_line S _ point hLetters
  have hWordMp : PositiveWord.represented S ((TripleWords.side S W s).get b)
      (Eq.mp (congrArg X (wordSource_sort S _)) (point (wordSource S _)))
      (Eq.mp (congrArg X (wordTarget_sort S _)) (point (wordTarget S _))) := by
    simpa only [cast_eq_mp] using hWord
  have hSource : Eq.mp (congrArg X (wordSource_sort S _))
      (point (wordSource S _)) = f.point (.inl (tripleSideSource s)) := by
    calc
      _ = sidePoint (thetaLeft S (TripleWords.side S W s)) :=
        cast_at_equal_vertex_mp (thetaVertexSort S (TripleWords.side S W s)) sidePoint
          (thetaBranchPosition_source S (TripleWords.side S W s) b)
          (thetaBranchPosition_sort S (TripleWords.side S W s) b (wordSource S _))
          (wordSource_sort S _)
      _ = _ := by cases s <;> rfl
  have hTarget : Eq.mp (congrArg X (wordTarget_sort S _))
      (point (wordTarget S _)) = f.point (.inl (tripleSideTarget s)) := by
    calc
      _ = sidePoint (thetaRight S (TripleWords.side S W s)) :=
        cast_at_equal_vertex_mp (thetaVertexSort S (TripleWords.side S W s)) sidePoint
          (thetaBranchPosition_target S (TripleWords.side S W s) b)
          (thetaBranchPosition_sort S (TripleWords.side S W s) b (wordTarget S _))
          (wordTarget_sort S _)
      _ = _ := by cases s <;> rfl
  rw [hSource,hTarget] at hWordMp
  exact hWordMp

end CCO.StrongExact
