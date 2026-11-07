import CCO.OldIdempotentForest.VisibleBranches
import CCO.GuardedOldSeams.LiftGraphTheta
import CCO.OldIdempotentForest.CycleContractionBranch

/-! Literal original-word lines read back on the ACTUAL shared-root
carrier. Only consecutive positions of the selected original branch are
asserted here: other branches may supply additional root shortcuts. No
realization of those other branches, CCO, SAP or source completion is an
input. Both orientations and singleton branches are retained. -/

universe u v w p q
namespace CCO.OldIdempotentForest

open CCO.StrongExact CCO.GuardedOldSeams CCO.GuardedTwoRoot

variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {P : Type p} {K : Type q} [Finite P] [Finite K]

namespace RootWordGeometry

variable (R : RootWordSystem S P K)

private theorem sigma_cast_point {s t : ι} (h : s = t) (x : X t) :
    (⟨s,Eq.mp (congrArg X h.symm) x⟩ : Sigma X) = ⟨t,x⟩ := by
  cases h
  rfl

private theorem sigma_eq_of_cast_eq {s t : ι} (h : s = t) (x : X s) (y : X t)
    (heq : h ▸ x = y) : (⟨s,x⟩ : Sigma X) = ⟨t,y⟩ := by
  cases h
  cases heq
  rfl

private theorem cast_point_eq_of_sigma_eq {s t : ι} (h : s = t)
    (x : X s) (y : X t) (heq : (⟨s,x⟩ : Sigma X) = ⟨t,y⟩) :
    Eq.mp (congrArg X h) x = y := by
  cases h
  have hxy : x = y := by simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using heq
  cases hxy
  rfl

private theorem transportAtomOption_comp
    {s t s' t' s'' t'' : ι} (hs : s = s') (ht : t = t')
    (hs' : s' = s'') (ht' : t' = t'') (edge : Option (S.Atom s'' t'')) :
    transportAtomOption S hs ht (transportAtomOption S hs' ht' edge) =
      transportAtomOption S (hs.trans hs') (ht.trans ht') edge := by
  cases hs
  cases ht
  cases hs'
  cases ht'
  rfl

private theorem colour_cast_point {s t s' t' : ι} (hs : s = s') (ht : t = t')
    (x : X s') (y : X t') :
    S.colour (Eq.mp (congrArg X hs.symm) x) (Eq.mp (congrArg X ht.symm) y) =
      transportAtomOption S hs ht (S.colour x y) := by
  cases hs
  cases ht
  rfl

/-- The sort transport belongs to this original word position and its
literal occurrence on the actual global carrier. -/
noncomputable def branchPositionLinePoint (b : Branch R)
    {x : X (R.sort (R.left b.1))} {y : X (R.sort (R.right b.1))}
    (line : LiteralLine S (branchWord R b) x y)
    (z : wordPositions S (branchWord R b)) :
    X (R.vertexSort (R.branchPosition b.1 b.2 z)) :=
  Eq.mp (congrArg X (R.branchPosition_sort b.1 b.2 z).symm) (line.point z)

theorem branchPositionLinePoint_image (b : Branch R)
    {x : X (R.sort (R.left b.1))} {y : X (R.sort (R.right b.1))}
    (line : LiteralLine S (branchWord R b) x y)
    (z : wordPositions S (branchWord R b)) :
    (⟨R.vertexSort (R.branchPosition b.1 b.2 z),
      branchPositionLinePoint R b line z⟩ : Sigma X) =
      ⟨wordPositionSort S (branchWord R b) z,line.point z⟩ :=
  sigma_cast_point (R.branchPosition_sort b.1 b.2 z) (line.point z)

/-- The actual union edge at every forward ORIGINAL letter is exactly
that letter, with only the necessary literal endpoint-sort transports. -/
theorem diagram_original_branch_letter (seed : RootWordSeeds S R) (b : Branch R)
    (e : wordEdgeIndex S (branchWord R b))
    (hne : R.branchPosition b.1 b.2 (wordEdgeSource S (branchWord R b) e) ≠
      R.branchPosition b.1 b.2 (wordEdgeTarget S (branchWord R b) e)) :
    (R.diagram seed).edge
      (R.branchPosition b.1 b.2 (wordEdgeSource S (branchWord R b) e))
      (R.branchPosition b.1 b.2 (wordEdgeTarget S (branchWord R b) e)) hne =
      transportAtomOption S
        (R.branchPosition_sort b.1 b.2 (wordEdgeSource S (branchWord R b) e))
        (R.branchPosition_sort b.1 b.2 (wordEdgeTarget S (branchWord R b) e))
        (some (wordEdgeAtom S (branchWord R b) e)) := by
  dsimp only [branchWord] at e hne ⊢
  let z := thetaBranchEdgeSource S (R.words b.1) b.2 e
  let t := thetaBranchEdgeTarget S (R.words b.1) b.2 e
  have hlocal : (thetaEdgesOfLiteralLines S (R.words b.1)
      (seed.left b.1) (seed.right b.1) (seed.lines b.1)).edge z t
      (thetaBranchEdge_distinct S (R.words b.1) b.2 e) =
      transportAtomOption S
        (thetaBranchPosition_sort S (R.words b.1) b.2 (wordEdgeSource S ((R.words b.1).get b.2) e))
        (thetaBranchPosition_sort S (R.words b.1) b.2 (wordEdgeTarget S ((R.words b.1).get b.2) e))
        (some (wordEdgeAtom S ((R.words b.1).get b.2) e)) := by
    rw [transportAtomOption_some]
    exact thetaEdgesOfLiteralLines_forward S (R.words b.1)
      (seed.left b.1) (seed.right b.1) (seed.lines b.1) b.2 e
  change (R.gluing seed).unionEdge (R.embed b.1 z) (R.embed b.1 t) hne = _
  refine ((R.gluing seed).unionEdge_on_piece b.1 z t hne).trans ?_
  change transportAtomOption S (R.embed_sort b.1 z) (R.embed_sort b.1 t)
    ((thetaEdgesOfLiteralLines S (R.words b.1)
      (seed.left b.1) (seed.right b.1) (seed.lines b.1)).edge z t _) = _
  rw [hlocal]
  exact transportAtomOption_comp
    (R.embed_sort b.1 z) (R.embed_sort b.1 t)
    (thetaBranchPosition_sort S (R.words b.1) b.2
      (wordEdgeSource S ((R.words b.1).get b.2) e))
    (thetaBranchPosition_sort S (R.words b.1) b.2
      (wordEdgeTarget S ((R.words b.1).get b.2) e))
    (some (wordEdgeAtom S ((R.words b.1).get b.2) e))

theorem branchPositionLinePoint_letter_colour (seed : RootWordSeeds S R) (b : Branch R)
    {x : X (R.sort (R.left b.1))} {y : X (R.sort (R.right b.1))}
    (line : LiteralLine S (branchWord R b) x y)
    (e : wordEdgeIndex S (branchWord R b))
    (hne : R.branchPosition b.1 b.2 (wordEdgeSource S (branchWord R b) e) ≠
      R.branchPosition b.1 b.2 (wordEdgeTarget S (branchWord R b) e)) :
    S.colour
      (branchPositionLinePoint R b line (wordEdgeSource S (branchWord R b) e))
      (branchPositionLinePoint R b line (wordEdgeTarget S (branchWord R b) e)) =
      (R.diagram seed).edge
        (R.branchPosition b.1 b.2 (wordEdgeSource S (branchWord R b) e))
        (R.branchPosition b.1 b.2 (wordEdgeTarget S (branchWord R b) e)) hne := by
  dsimp only [branchWord] at line e hne ⊢
  let hs := R.branchPosition_sort b.1 b.2 (wordEdgeSource S ((R.words b.1).get b.2) e)
  let ht := R.branchPosition_sort b.1 b.2 (wordEdgeTarget S ((R.words b.1).get b.2) e)
  have hc : S.colour
      (branchPositionLinePoint R b line (wordEdgeSource S ((R.words b.1).get b.2) e))
      (branchPositionLinePoint R b line (wordEdgeTarget S ((R.words b.1).get b.2) e)) =
      transportAtomOption S hs ht
        (S.colour (line.point (wordEdgeSource S ((R.words b.1).get b.2) e))
          (line.point (wordEdgeTarget S ((R.words b.1).get b.2) e))) :=
    colour_cast_point hs ht _ _
  exact hc.trans ((congrArg (transportAtomOption S hs ht) (line.edges e)).trans
    (diagram_original_branch_letter R seed b e hne).symm)

/-- Both orientations preserve the actual stored original atom. Only
adjacent letters of THIS word are asserted, not shortcut root edges. -/
theorem branchPositionLine_preserves_adjacent (seed : RootWordSeeds S R) (b : Branch R)
    {x : X (R.sort (R.left b.1))} {y : X (R.sort (R.right b.1))}
    (line : LiteralLine S (branchWord R b) x y)
    (z t : wordPositions S (branchWord R b))
    (hadj : ∃ e : wordEdgeIndex S (branchWord R b),
      (wordEdgeSource S (branchWord R b) e = z ∧ wordEdgeTarget S (branchWord R b) e = t) ∨
      (wordEdgeSource S (branchWord R b) e = t ∧ wordEdgeTarget S (branchWord R b) e = z))
    (hne : R.branchPosition b.1 b.2 z ≠ R.branchPosition b.1 b.2 t)
    (a : S.Atom (R.vertexSort (R.branchPosition b.1 b.2 z))
      (R.vertexSort (R.branchPosition b.1 b.2 t)))
    (ha : (R.diagram seed).edge (R.branchPosition b.1 b.2 z)
      (R.branchPosition b.1 b.2 t) hne = some a) :
    S.colour (branchPositionLinePoint R b line z) (branchPositionLinePoint R b line t) = some a := by
  obtain ⟨e,(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩ := hadj
  · exact (branchPositionLinePoint_letter_colour R seed b line e hne).trans ha
  · have hf := ((R.diagram seed).edge_reverse _ _ hne a).mp ha
    have hc := (branchPositionLinePoint_letter_colour R seed b line e hne.symm).trans hf
    exact (S.colour_swap _ _ a).mpr hc

/-- Points indexed by the canonical original position order. -/
noncomputable def branchLinePoint (b : Branch R)
    {x : X (R.sort (R.left b.1))} {y : X (R.sort (R.right b.1))}
    (line : LiteralLine S (branchWord R b) x y)
    (k : Fin (TypedPrefix.length S (branchWord R b) + 1)) :
    X (R.vertexSort (indexedVertex R b k)) :=
  branchPositionLinePoint R b line ((wordPositionEquiv S (branchWord R b)).symm k)

theorem branchLinePoint_image (b : Branch R)
    {x : X (R.sort (R.left b.1))} {y : X (R.sort (R.right b.1))}
    (line : LiteralLine S (branchWord R b) x y)
    (k : Fin (TypedPrefix.length S (branchWord R b) + 1)) :
    (⟨R.vertexSort (indexedVertex R b k),branchLinePoint R b line k⟩ : Sigma X) =
      ⟨wordPositionSort S (branchWord R b) ((wordPositionEquiv S (branchWord R b)).symm k),
        line.point ((wordPositionEquiv S (branchWord R b)).symm k)⟩ :=
  branchPositionLinePoint_image R b line _

theorem branchLinePoint_first_image (b : Branch R)
    {x : X (R.sort (R.left b.1))} {y : X (R.sort (R.right b.1))}
    (line : LiteralLine S (branchWord R b) x y) :
    (⟨R.vertexSort (indexedVertex R b 0),branchLinePoint R b line 0⟩ : Sigma X) =
      ⟨R.sort (R.left b.1),x⟩ := by
  rw [branchLinePoint_image]
  have hs : (wordPositionEquiv S (branchWord R b)).symm 0 = wordSource S (branchWord R b) := by
    apply (wordPositionEquiv S (branchWord R b)).injective
    simp
  rw [hs]
  exact sigma_eq_of_cast_eq (wordSource_sort S (branchWord R b)) _ _ line.source

theorem branchLinePoint_last_image (b : Branch R)
    {x : X (R.sort (R.left b.1))} {y : X (R.sort (R.right b.1))}
    (line : LiteralLine S (branchWord R b) x y) :
    (⟨R.vertexSort (indexedVertex R b (Fin.last (TypedPrefix.length S (branchWord R b)))),
      branchLinePoint R b line (Fin.last (TypedPrefix.length S (branchWord R b)))⟩ : Sigma X) =
      ⟨R.sort (R.right b.1),y⟩ := by
  rw [branchLinePoint_image]
  have ht : (wordPositionEquiv S (branchWord R b)).symm
      (Fin.last (TypedPrefix.length S (branchWord R b))) = wordTarget S (branchWord R b) := by
    apply (wordPositionEquiv S (branchWord R b)).injective
    simp
  rw [ht]
  exact sigma_eq_of_cast_eq (wordTarget_sort S (branchWord R b)) _ _ line.target

theorem branchLinePoint_first (b : Branch R)
    {x : X (R.sort (R.left b.1))} {y : X (R.sort (R.right b.1))}
    (line : LiteralLine S (branchWord R b) x y) :
    Eq.mp (congrArg X (congrArg R.vertexSort (indexedVertex_first R b)))
      (branchLinePoint R b line 0) = x :=
  cast_point_eq_of_sigma_eq (congrArg R.vertexSort (indexedVertex_first R b))
    _ _ (branchLinePoint_first_image R b line)

theorem branchLinePoint_last (b : Branch R)
    {x : X (R.sort (R.left b.1))} {y : X (R.sort (R.right b.1))}
    (line : LiteralLine S (branchWord R b) x y) :
    Eq.mp (congrArg X (congrArg R.vertexSort (indexedVertex_last R b)))
      (branchLinePoint R b line (Fin.last (TypedPrefix.length S (branchWord R b)))) = y :=
  cast_point_eq_of_sigma_eq (congrArg R.vertexSort (indexedVertex_last R b))
    _ _ (branchLinePoint_last_image R b line)

theorem branchLinePoint_injective (b : Branch R)
    {x : X (R.sort (R.left b.1))} {y : X (R.sort (R.right b.1))}
    (line : LiteralLine S (branchWord R b) x y)
    (hinj : Function.Injective (fun z : wordPositions S (branchWord R b) =>
      (⟨wordPositionSort S (branchWord R b) z,line.point z⟩ : Sigma X))) :
    Function.Injective (fun k : Fin (TypedPrefix.length S (branchWord R b) + 1) =>
      (⟨R.vertexSort (indexedVertex R b k),branchLinePoint R b line k⟩ : Sigma X)) := by
  intro k l hkl
  apply (wordPositionEquiv S (branchWord R b)).symm.injective
  apply hinj
  exact (branchLinePoint_image R b line k).symm.trans
    (hkl.trans (branchLinePoint_image R b line l))

/-- A line for the exact selected original word preserves every actual
stored cycle-edge atom along that branch, in either traversal orientation. -/
theorem branchLine_preserves_step (seed : RootWordSeeds S R) (b : Branch R)
    {x : X (R.sort (R.left b.1))} {y : X (R.sort (R.right b.1))}
    (line : LiteralLine S (branchWord R b) x y)
    (s t : Fin (TypedPrefix.length S (branchWord R b) + 1))
    (hadj : s.val + 1 = t.val ∨ t.val + 1 = s.val)
    (hne : indexedVertex R b s ≠ indexedVertex R b t)
    (a : S.Atom (R.vertexSort (indexedVertex R b s)) (R.vertexSort (indexedVertex R b t)))
    (ha : (R.diagram seed).edge (indexedVertex R b s) (indexedVertex R b t) hne = some a) :
    S.colour (branchLinePoint R b line s) (branchLinePoint R b line t) = some a := by
  let z := (wordPositionEquiv S (branchWord R b)).symm s
  let u := (wordPositionEquiv S (branchWord R b)).symm t
  have hpositions : (wordPositionEquiv S (branchWord R b) z).val + 1 =
      (wordPositionEquiv S (branchWord R b) u).val ∨
      (wordPositionEquiv S (branchWord R b) u).val + 1 =
        (wordPositionEquiv S (branchWord R b) z).val := by
    simpa only [z,u,Equiv.apply_symm_apply] using hadj
  exact branchPositionLine_preserves_adjacent R seed b line z u
    ((original_word_adjacent_iff S (branchWord R b) z u).mpr hpositions) hne a ha

section Traversal

open CycleGeometry

variable {R} {Q : RootFreePath (privateBranchSystem R)}

/-- The derived traversal's position map follows consecutive ORIGINAL
indices, forwards or backwards according to its recorded orientation. -/
theorem traversal_position_adjacent (T : Q.OriginalBranchTraversal) (d : Fin Q.length) :
    (T.position d.castSucc).val + 1 = (T.position d.succ).val ∨
      (T.position d.succ).val + 1 = (T.position d.castSucc).val := by
  have hs := T.rank d.castSucc
  have ht := T.rank d.succ
  have hd := d.isLt
  have hlen : Q.length = TypedPrefix.length S (branchWord R T.branch) := T.length_eq
  change (T.position d.castSucc).val =
    (if T.forward then d.val else TypedPrefix.length S (branchWord R T.branch) - d.val) at hs
  change (T.position d.succ).val =
    (if T.forward then d.val + 1 else TypedPrefix.length S (branchWord R T.branch) - (d.val + 1)) at ht
  cases hforward : T.forward with
  | false =>
      right
      simp only [hforward,Bool.false_eq_true,ite_false] at hs ht
      omega
  | true =>
      left
      simp only [hforward,ite_true] at hs ht
      omega

/-- Reindex one original word line along the ACTUALLY derived simple
root-to-root arc, with its exact original position equality. -/
noncomputable def traversalLinePoint (T : Q.OriginalBranchTraversal)
    {x : X (R.sort (R.left T.branch.1))} {y : X (R.sort (R.right T.branch.1))}
    (line : LiteralLine S (branchWord R T.branch) x y)
    (d : Fin (Q.length + 1)) : X (R.vertexSort (Q.vertex d)) :=
  Eq.mp (congrArg X (congrArg R.vertexSort (T.point d)).symm)
    (branchLinePoint R T.branch line (T.position d))

theorem traversalLinePoint_image (T : Q.OriginalBranchTraversal)
    {x : X (R.sort (R.left T.branch.1))} {y : X (R.sort (R.right T.branch.1))}
    (line : LiteralLine S (branchWord R T.branch) x y) (d : Fin (Q.length + 1)) :
    (⟨R.vertexSort (Q.vertex d),traversalLinePoint T line d⟩ : Sigma X) =
      ⟨R.vertexSort (indexedVertex R T.branch (T.position d)),
        branchLinePoint R T.branch line (T.position d)⟩ :=
  sigma_cast_point (congrArg R.vertexSort (T.point d)) _

private theorem preserves_reindexed_vertices {D : PartialDiagram S R.Vertex}
    {s t s' t' : R.Vertex} (hs : s = s') (ht : t = t')
    (x : X (D.vertexSort s')) (y : X (D.vertexSort t'))
    (hpres : ∀ (hne : s' ≠ t') (a : S.Atom (D.vertexSort s') (D.vertexSort t')),
      D.edge s' t' hne = some a → S.colour x y = some a)
    (hne : s ≠ t) (a : S.Atom (D.vertexSort s) (D.vertexSort t))
    (ha : D.edge s t hne = some a) :
    S.colour (Eq.mp (congrArg X (congrArg D.vertexSort hs).symm) x)
      (Eq.mp (congrArg X (congrArg D.vertexSort ht).symm) y) = some a := by
  cases hs
  cases ht
  exact hpres hne a ha

/-- Every edge of the actual original arc keeps its specified old atom
when that exact original branch word is realized at new endpoints. -/
theorem traversalLine_preserves_step (seed : RootWordSeeds S R)
    (T : Q.OriginalBranchTraversal)
    {x : X (R.sort (R.left T.branch.1))} {y : X (R.sort (R.right T.branch.1))}
    (line : LiteralLine S (branchWord R T.branch) x y) (d : Fin Q.length)
    (hne : Q.vertex d.castSucc ≠ Q.vertex d.succ)
    (a : S.Atom (R.vertexSort (Q.vertex d.castSucc)) (R.vertexSort (Q.vertex d.succ)))
    (ha : (R.diagram seed).edge (Q.vertex d.castSucc) (Q.vertex d.succ) hne = some a) :
    S.colour (traversalLinePoint T line d.castSucc) (traversalLinePoint T line d.succ) = some a := by
  apply preserves_reindexed_vertices (D := R.diagram seed)
    (T.point d.castSucc) (T.point d.succ)
    (branchLinePoint R T.branch line (T.position d.castSucc))
    (branchLinePoint R T.branch line (T.position d.succ)) ?_ hne a ha
  intro hst b hb
  exact branchLine_preserves_step R seed T.branch line _ _
    (traversal_position_adjacent T d) hst b hb

end Traversal

end RootWordGeometry
end CCO.OldIdempotentForest
