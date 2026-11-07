import CCO.GuardedOldSeams.LiftGraphVertices
import CCO.GuardedOldSeams.LiftGraphGluing
import CCO.StrongExact.ThetaFamilySemantics

/-! The local theta pieces are actual original-colour diagrams obtained
from one common fine-pair seed. Their literal edges are independent of
the choice of new walks realizing those same original branch words. -/

universe u v a p q

namespace CCO.GuardedOldSeams

open StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,a} ι X)

theorem theta_literal_lines_adjacent_colours {i j : ι}
    (words : List (PositiveWord S i j)) (x x' : X i) (y y' : X j)
    (lines : ∀ b, LiteralLine S (words.get b) x y)
    (lines' : ∀ b, LiteralLine S (words.get b) x' y')
    (z t : thetaVertices S words) (hadj : thetaAdjacent S words z t) :
    S.colour (thetaFamilyLinePoint S words x y lines z)
        (thetaFamilyLinePoint S words x y lines t) =
      S.colour (thetaFamilyLinePoint S words x' y' lines' z)
        (thetaFamilyLinePoint S words x' y' lines' t) := by
  classical
  obtain ⟨arc, ha, rfl, rfl⟩ := hadj
  unfold thetaArcs at ha
  obtain ⟨b, _, hc⟩ := List.mem_flatMap.mp ha
  obtain ⟨candidate, hc, ha⟩ := List.mem_flatMap.mp hc
  unfold thetaBranchArcs at hc
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hc
  have hcases : arc = thetaForwardArc S words b e ∨
      arc = (thetaForwardArc S words b e).reverse := by simpa using ha
  rcases hcases with rfl | rfl
  · exact (thetaFamilyLinePoint_letter S words x y lines b e).trans
      (thetaFamilyLinePoint_letter S words x' y' lines' b e).symm
  · have h := (S.colour_swap _ _ (thetaBranchEdgeAtom S words b e)).mp
      (thetaFamilyLinePoint_letter S words x y lines b e)
    have h' := (S.colour_swap _ _ (thetaBranchEdgeAtom S words b e)).mp
      (thetaFamilyLinePoint_letter S words x' y' lines' b e)
    exact h.trans h'.symm

noncomputable def thetaHomOfOtherLiteralLines {i j : ι}
    (words : List (PositiveWord S i j)) (x x' : X i) (y y' : X j)
    (lines : ∀ b, LiteralLine S (words.get b) x y)
    (lines' : ∀ b, LiteralLine S (words.get b) x' y') :
    DiagramHom (thetaEdgesOfLiteralLines S words x y lines).toDiagram where
  point := thetaFamilyLinePoint S words x' y' lines'
  preserves_edge := by
    classical
    intro z t hzt b hb
    change (if thetaAdjacent S words z t then
      S.colour (thetaFamilyLinePoint S words x y lines z)
        (thetaFamilyLinePoint S words x y lines t) else none) = some b at hb
    by_cases ha : thetaAdjacent S words z t
    · rw [ite_eq_left ha] at hb
      exact (theta_literal_lines_adjacent_colours S words x x' y y' lines lines' z t ha).symm.trans hb
    · simp only [ite_eq_right ha, reduceCtorEq] at hb

def transportAtomOption {s t s' t' : ι} (hs : s = s') (ht : t = t')
    (edge : Option (S.Atom s' t')) : Option (S.Atom s t) :=
  hs.symm ▸ (ht.symm ▸ edge)

def transportAtom {s t s' t' : ι} (hs : s = s') (ht : t = t')
    (b : S.Atom s' t') : S.Atom s t := hs.symm ▸ (ht.symm ▸ b)

theorem transportAtomOption_some {s t s' t' : ι} (hs : s = s') (ht : t = t')
    (b : S.Atom s' t') :
    transportAtomOption S hs ht (some b) = some (transportAtom S hs ht b) := by
  cases hs
  cases ht
  rfl

theorem colour_of_transportAtom {s t s' t' : ι} (hs : s = s') (ht : t = t')
    (x : X s) (y : X t) (b : S.Atom s' t')
    (h : S.colour x y = some (transportAtom S hs ht b)) :
    S.colour (Eq.mp (congrArg X hs) x) (Eq.mp (congrArg X ht) y) = some b := by
  cases hs
  cases ht
  exact h

theorem transportAtomOption_reverse {s t s' t' : ι} (hs : s = s') (ht : t = t')
    (edge : Option (S.Atom s' t')) (reverse : Option (S.Atom t' s'))
    (h : ∀ b, edge = some b ↔ reverse = some (S.conv b)) (b : S.Atom s t) :
    transportAtomOption S hs ht edge = some b ↔
      transportAtomOption S ht hs reverse = some (S.conv b) := by
  cases hs
  cases ht
  exact h b

theorem transportAtomOption_colour {s t s' t' : ι} (hs : s = s') (ht : t = t')
    (edge : Option (S.Atom s' t')) (x : X s) (y : X t)
    (h : ∀ b, edge = some b → S.colour (hs ▸ x) (ht ▸ y) = some b)
    (b : S.Atom s t) (hb : transportAtomOption S hs ht edge = some b) :
    S.colour x y = some b := by
  cases hs
  cases ht
  exact h b hb

variable {P : Type p} {K : Type q} [Finite P] [Finite K]

structure RootWordSeeds (R : RootWordSystem S P K) where
  left : ∀ k, X (R.sort (R.left k))
  right : ∀ k, X (R.sort (R.right k))
  lines : ∀ k b, LiteralLine S ((R.words k).get b) (left k) (right k)

namespace RootWordSystem

variable {S} (R : RootWordSystem S P K) (seed : RootWordSeeds S R)

noncomputable def gluing : DiagramGluing S R.Vertex K where
  sort := R.vertexSort
  piece k := thetaVertices S (R.words k)
  embed := R.embed
  embed_injective := R.embed_injective
  overlap_unique k l z t z' t' hz ht hne := R.embed_overlap_unique k l z t z' t' hne hz ht
  edge k z t h := transportAtomOption S (R.embed_sort k z) (R.embed_sort k t)
    ((thetaEdgesOfLiteralLines S (R.words k) (seed.left k) (seed.right k) (seed.lines k)).edge z t h)
  edge_reverse k z t h b := transportAtomOption_reverse S
    (R.embed_sort k z) (R.embed_sort k t) _ _
    ((thetaEdgesOfLiteralLines S (R.words k) (seed.left k) (seed.right k) (seed.lines k)).edge_reverse z t h) b

noncomputable def diagram : PartialDiagram S R.Vertex := (R.gluing seed).toDiagram

def familyPoint (root : ∀ p, X (R.sort p))
    (lines : ∀ k b, LiteralLine S ((R.words k).get b) (root (R.left k)) (root (R.right k))) :
    ∀ z : R.Vertex, X (R.vertexSort z)
  | .inl p => root p
  | .inr ⟨k,b,z⟩ => (lines k b).point z.val

theorem familyPoint_embed (root : ∀ p, X (R.sort p))
    (lines : ∀ k b, LiteralLine S ((R.words k).get b) (root (R.left k)) (root (R.right k)))
    (k : K) (z : thetaVertices S (R.words k)) :
    (R.embed_sort k z) ▸ R.familyPoint root lines (R.embed k z) =
      thetaFamilyLinePoint S (R.words k) (root (R.left k)) (root (R.right k)) (lines k) z := by
  cases z with
  | inl b => cases b <;> rfl
  | inr z => rfl

noncomputable def homOfLines (root : ∀ p, X (R.sort p))
    (lines : ∀ k b, LiteralLine S ((R.words k).get b) (root (R.left k)) (root (R.right k))) :
    DiagramHom (R.diagram seed) := by
  apply (R.gluing seed).homOfPieces (R.familyPoint root lines)
  intro k z t hzt b hb
  dsimp only [gluing] at z t hzt b hb ⊢
  apply transportAtomOption_colour S (R.embed_sort k z) (R.embed_sort k t) _ _ _ ?_ b hb
  intro c hc
  change S.colour ((R.embed_sort k z) ▸ R.familyPoint root lines (R.embed k z))
    ((R.embed_sort k t) ▸ R.familyPoint root lines (R.embed k t)) = some c
  rw [familyPoint_embed, familyPoint_embed]
  exact (thetaHomOfOtherLiteralLines S (R.words k) (seed.left k) (root (R.left k))
    (seed.right k) (root (R.right k)) (seed.lines k) (lines k)).preserves_edge z t hzt c hc

/-- Every local original theta diagram is retained by the global union,
including coincident singleton branch letters on its root pair. -/
noncomputable def restrictTheta (f : DiagramHom (R.diagram seed)) (k : K) :
    DiagramHom (thetaEdgesOfLiteralLines S (R.words k) (seed.left k)
      (seed.right k) (seed.lines k)).toDiagram where
  point z := Eq.mp (congrArg X (R.embed_sort k z)) (f.point (R.embed k z))
  preserves_edge := by
    intro z t hzt b hb
    change S.Atom (thetaVertexSort S (R.words k) z) (thetaVertexSort S (R.words k) t) at b
    change (thetaEdgesOfLiteralLines S (R.words k) (seed.left k) (seed.right k)
      (seed.lines k)).edge z t hzt = some b at hb
    change S.colour (Eq.mp (congrArg X (R.embed_sort k z)) (f.point (R.embed k z)))
      (Eq.mp (congrArg X (R.embed_sort k t)) (f.point (R.embed k t))) = some b
    have hg : (R.gluing seed).edge k z t hzt =
        some (transportAtom S (R.embed_sort k z) (R.embed_sort k t) b) := by
      change transportAtomOption S (R.embed_sort k z) (R.embed_sort k t)
        ((thetaEdgesOfLiteralLines S (R.words k) (seed.left k) (seed.right k)
          (seed.lines k)).edge z t hzt) = _
      rw [hb, transportAtomOption_some]
    have hc := (R.gluing seed).hom_preserves_piece f k z t hzt _ hg
    simpa only [gluing] using
      (colour_of_transportAtom S (R.embed_sort k z) (R.embed_sort k t) _ _ b hc)

end RootWordSystem
end CCO.GuardedOldSeams
