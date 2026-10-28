import CCO.StrongExact.ThetaPairLineMap
import CCO.StrongExact.ThetaWholeReadout
import CCO.StrongExact.Survivors

/-!
# General private-word theta semantics from literal original lines

A family of actual word lines with shared real endpoints supplies a typed
point map on all private theta vertices. Recording only genuine word
adjacencies and reading their actual old colours automatically merges
compatible duplicate direct branches. This construction is used only when
a common profile atom is already GIVEN; it does not assume or replace
word Helly or the cycle argument proving that atom exists.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

private theorem line_sigma_eq_of_cast {s t : ι} (h : s = t)
    (x : X s) (y : X t) (hc : h ▸ x = y) :
    (⟨s,x⟩ : Sigma X) = ⟨t,y⟩ := by
  cases h
  cases hc
  rfl

private theorem line_cast_of_sigma_eq {s t : ι} (h : s = t)
    (x : X s) (y : X t)
    (hc : (⟨s,x⟩ : Sigma X) = ⟨t,y⟩) : h ▸ x = y := by
  cases hc
  rfl

private theorem line_colour_uncast_both
    {s t s' t' : ι} (hs : s = s') (ht : t = t')
    (a : S.Atom s' t') (x : X s) (y : X t)
    (hxy : S.colour (hs ▸ x) (ht ▸ y) = some a) :
    S.colour x y = some (hs.symm ▸ (ht.symm ▸ a)) := by
  cases hs
  cases ht
  simpa using hxy

/-- One original typed point per theta vertex, with shared roots. -/
noncomputable def thetaFamilyLinePoint
    (ws : List (PositiveWord S i j)) (x : X i) (y : X j)
    (lines : ∀ b : Fin ws.length, LiteralLine S (ws.get b) x y) :
    ∀ z : thetaVertices S ws, X (thetaVertexSort S ws z)
  | .inl false => x
  | .inl true => y
  | .inr ⟨b,t⟩ => (lines b).point t.val

/-- Each chosen line is preserved literally at every formal position. -/
theorem thetaFamilyLinePoint_image
    (ws : List (PositiveWord S i j)) (x : X i) (y : X j)
    (lines : ∀ b : Fin ws.length, LiteralLine S (ws.get b) x y)
    (b : Fin ws.length) (z : wordPositions S (ws.get b)) :
    (⟨thetaVertexSort S ws (thetaBranchPosition S ws b z),
      thetaFamilyLinePoint S ws x y lines
        (thetaBranchPosition S ws b z)⟩ : Sigma X) =
      ⟨wordPositionSort S (ws.get b) z, (lines b).point z⟩ := by
  classical
  by_cases hSource : z = wordSource S (ws.get b)
  · subst z
    rw [thetaBranchPosition_source S ws b]
    exact (line_sigma_eq_of_cast (wordSource_sort S (ws.get b))
      ((lines b).point (wordSource S (ws.get b))) x (lines b).source).symm
  · by_cases hTarget : z = wordTarget S (ws.get b)
    · subst z
      rw [thetaBranchPosition_target S ws b]
      exact (line_sigma_eq_of_cast (wordTarget_sort S (ws.get b))
        ((lines b).point (wordTarget S (ws.get b))) y (lines b).target).symm
    · let t : wordInterior S (ws.get b) := ⟨z,hSource,hTarget⟩
      have hz := thetaBranchPosition_interior S ws b t
      change thetaBranchPosition S ws b z = _ at hz
      rw [hz]
      rfl

/-- A common-root family map respects every ORIGINAL word letter,
without any long-word restriction or a pre-existing edge provider. -/
theorem thetaFamilyLinePoint_letter
    (ws : List (PositiveWord S i j)) (x : X i) (y : X j)
    (lines : ∀ b : Fin ws.length, LiteralLine S (ws.get b) x y)
    (b : Fin ws.length) (e : wordEdgeIndex S (ws.get b)) :
    S.colour
      (thetaFamilyLinePoint S ws x y lines (thetaBranchEdgeSource S ws b e))
      (thetaFamilyLinePoint S ws x y lines (thetaBranchEdgeTarget S ws b e)) =
      some (thetaBranchEdgeAtom S ws b e) := by
  rw [thetaBranchEdgeAtom_cast S ws b e]
  apply line_colour_uncast_both S
    (thetaBranchPosition_sort S ws b (wordEdgeSource S (ws.get b) e))
    (thetaBranchPosition_sort S ws b (wordEdgeTarget S (ws.get b) e))
  have hs := line_cast_of_sigma_eq
    (thetaBranchPosition_sort S ws b (wordEdgeSource S (ws.get b) e))
    (thetaFamilyLinePoint S ws x y lines (thetaBranchEdgeSource S ws b e))
    ((lines b).point (wordEdgeSource S (ws.get b) e))
    (thetaFamilyLinePoint_image S ws x y lines b
      (wordEdgeSource S (ws.get b) e))
  have ht := line_cast_of_sigma_eq
    (thetaBranchPosition_sort S ws b (wordEdgeTarget S (ws.get b) e))
    (thetaFamilyLinePoint S ws x y lines (thetaBranchEdgeTarget S ws b e))
    ((lines b).point (wordEdgeTarget S (ws.get b) e))
    (thetaFamilyLinePoint_image S ws x y lines b
      (wordEdgeTarget S (ws.get b) e))
  rw [hs,ht]
  exact (lines b).edges e

/-- The actual original-colour diagram records only genuine private
word adjacencies. All duplicate direct edges are ONE optional atom,
as read from the given common-root realization. -/
noncomputable def thetaEdgesOfLiteralLines
    (ws : List (PositiveWord S i j)) (x : X i) (y : X j)
    (lines : ∀ b : Fin ws.length, LiteralLine S (ws.get b) x y) :
    ThetaEdges S ws := by
  classical
  let point := thetaFamilyLinePoint S ws x y lines
  refine ⟨(fun z t _ =>
    if thetaAdjacent S ws z t then S.colour (point z) (point t) else none), ?_⟩
  intro z t hzt a
  by_cases hAdj : thetaAdjacent S ws z t
  · have hRev := thetaAdjacent_symmetric S ws hAdj
    simp only [ite_eq_left hAdj, ite_eq_left hRev]
    exact S.colour_swap (point z) (point t) a
  · have hRev : ¬ thetaAdjacent S ws t z := by
      intro h
      exact hAdj (thetaAdjacent_symmetric S ws h)
    simp [hAdj,hRev]

/-- Each original diversity letter is a literal specified edge. -/
theorem thetaEdgesOfLiteralLines_forward
    (ws : List (PositiveWord S i j)) (x : X i) (y : X j)
    (lines : ∀ b : Fin ws.length, LiteralLine S (ws.get b) x y)
    (b : Fin ws.length) (e : wordEdgeIndex S (ws.get b)) :
    (thetaEdgesOfLiteralLines S ws x y lines).edge
      (thetaBranchEdgeSource S ws b e) (thetaBranchEdgeTarget S ws b e)
      (thetaBranchEdge_distinct S ws b e) =
      some (thetaBranchEdgeAtom S ws b e) := by
  classical
  change (if thetaAdjacent S ws
      (thetaBranchEdgeSource S ws b e) (thetaBranchEdgeTarget S ws b e)
    then S.colour
      (thetaFamilyLinePoint S ws x y lines (thetaBranchEdgeSource S ws b e))
      (thetaFamilyLinePoint S ws x y lines (thetaBranchEdgeTarget S ws b e))
    else none) = _
  rw [ite_eq_left (thetaAdjacent_forward S ws b e)]
  exact thetaFamilyLinePoint_letter S ws x y lines b e

/-- The given line family itself is an actual homomorphism. -/
noncomputable def thetaHomOfLiteralLines
    (ws : List (PositiveWord S i j)) (x : X i) (y : X j)
    (lines : ∀ b : Fin ws.length, LiteralLine S (ws.get b) x y) :
    DiagramHom ((thetaEdgesOfLiteralLines S ws x y lines).toDiagram) where
  point := thetaFamilyLinePoint S ws x y lines
  preserves_edge := by
    classical
    intro z t hzt a ha
    change (if thetaAdjacent S ws z t then
      S.colour (thetaFamilyLinePoint S ws x y lines z)
        (thetaFamilyLinePoint S ws x y lines t) else none) = some a at ha
    change S.colour (thetaFamilyLinePoint S ws x y lines z)
      (thetaFamilyLinePoint S ws x y lines t) = some a
    by_cases hAdj : thetaAdjacent S ws z t
    · rw [ite_eq_left hAdj] at ha
      exact ha
    · simp [hAdj] at ha

/-- Generic whole-word readout for any actual theta edges retaining
all original forward letters. There is no conditional source provider. -/
theorem thetaEdges_representsWords_of_forward
    (ws : List (PositiveWord S i j)) (T : ThetaEdges S ws)
    (hForward : ∀ (b : Fin ws.length) (e : wordEdgeIndex S (ws.get b)),
      T.edge (thetaBranchEdgeSource S ws b e) (thetaBranchEdgeTarget S ws b e)
        (thetaBranchEdge_distinct S ws b e) =
        some (thetaBranchEdgeAtom S ws b e)) :
    T.RepresentsWords := by
  intro f word hw
  obtain ⟨b,hb⟩ := List.mem_iff_get.mp hw
  subst word
  let point : ∀ z : wordPositions S (ws.get b),
      X (wordPositionSort S (ws.get b) z) :=
    fun z => (thetaBranchPosition_sort S ws b z) ▸
      f.point (thetaBranchPosition S ws b z)
  have hLetters : ∀ e : wordEdgeIndex S (ws.get b),
      S.colour (point (wordEdgeSource S (ws.get b) e))
        (point (wordEdgeTarget S (ws.get b) e)) =
        some (wordEdgeAtom S (ws.get b) e) := by
    intro e
    have he := f.preserves_edge
      (thetaBranchEdgeSource S ws b e) (thetaBranchEdgeTarget S ws b e)
      (thetaBranchEdge_distinct S ws b e) (thetaBranchEdgeAtom S ws b e)
      (hForward b e)
    rw [thetaBranchEdgeAtom_cast S ws b e] at he
    exact colour_cast_both S
      (thetaBranchPosition_sort S ws b (wordEdgeSource S (ws.get b) e))
      (thetaBranchPosition_sort S ws b (wordEdgeTarget S (ws.get b) e))
      (wordEdgeAtom S (ws.get b) e)
      (f.point (thetaBranchEdgeSource S ws b e))
      (f.point (thetaBranchEdgeTarget S ws b e)) he
  have hWord := represented_of_literal_word_line S (ws.get b) point hLetters
  have hWordMp : PositiveWord.represented S (ws.get b)
      (Eq.mp (congrArg X (wordSource_sort S (ws.get b)))
        (point (wordSource S (ws.get b))))
      (Eq.mp (congrArg X (wordTarget_sort S (ws.get b)))
        (point (wordTarget S (ws.get b)))) := by
    simpa only [cast_eq_mp] using hWord
  have hs : Eq.mp (congrArg X (wordSource_sort S (ws.get b)))
      (point (wordSource S (ws.get b))) = f.point (thetaLeft S ws) :=
    cast_at_equal_vertex_mp (thetaVertexSort S ws) f.point
      (thetaBranchPosition_source S ws b)
      (thetaBranchPosition_sort S ws b (wordSource S (ws.get b)))
      (wordSource_sort S (ws.get b))
  have ht : Eq.mp (congrArg X (wordTarget_sort S (ws.get b)))
      (point (wordTarget S (ws.get b))) = f.point (thetaRight S ws) :=
    cast_at_equal_vertex_mp (thetaVertexSort S ws) f.point
      (thetaBranchPosition_target S ws b)
      (thetaBranchPosition_sort S ws b (wordTarget S (ws.get b)))
      (wordTarget_sort S (ws.get b))
  rw [hs,ht] at hWordMp
  exact hWordMp

/-- Every homomorphism of the actual common-root line diagram
realizes all original presented positive words. -/
theorem thetaEdgesOfLiteralLines_representsWords
    (ws : List (PositiveWord S i j)) (x : X i) (y : X j)
    (lines : ∀ b : Fin ws.length, LiteralLine S (ws.get b) x y) :
    (thetaEdgesOfLiteralLines S ws x y lines).RepresentsWords :=
  thetaEdges_representsWords_of_forward S ws _
    (thetaEdgesOfLiteralLines_forward S ws x y lines)

end CCO.StrongExact
