import CCO.StrongExact.PathCycleSupport
import CCO.PairHomogeneity

/-!
# Actual finite line witnesses from stable STRONG support

A line below has an injective list of formal vertices. Its witness may
identify nonadjacent real points. The endpoint atom and every adjacent
atom come from the displayed stable network. This is a direct typed
induction through genuine three-point strong triangles and original pair
homogeneity. It does not replace simple paths by arbitrary walks.
-/

universe u v w z
namespace CCO.StrongPC
variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

def lineEndpointPair {n : Nat} (vertices : Fin (n + 2) ↪ V) : DistinctPair V :=
  ⟨vertices 0, vertices (Fin.last (n + 1)), by
    intro h
    have hv := congrArg Fin.val (vertices.injective h)
    simp at hv⟩

def lineStepPair {n : Nat} (vertices : Fin (n + 2) ↪ V)
    (p : Fin (n + 1)) : DistinctPair V :=
  ⟨vertices p.castSucc, vertices p.succ, by
    intro h
    have hv := congrArg Fin.val (vertices.injective h)
    simp at hv⟩

/-- Stable support along an injectively enumerated formal line has an
actual original-sort realization, preserving its selected endpoint atom.
No SAP, CCO or exact Helly provider is needed in this line induction. -/
theorem stable_line_realizable
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (N : Network D) (hStable : Stable D N) :
    ∀ (n : Nat) (vertices : Fin (n + 2) ↪ V)
      (a : S.Atom (D.vertexSort (vertices 0))
        (D.vertexSort (vertices (Fin.last (n + 1))))),
      a ∈ N (lineEndpointPair vertices) →
      ∃ point : ∀ p : Fin (n + 2), X (D.vertexSort (vertices p)),
        (∀ p : Fin (n + 1), ∃ b,
          b ∈ N (lineStepPair vertices p) ∧
          S.colour (point p.castSucc) (point p.succ) = some b) ∧
        S.colour (point 0) (point (Fin.last (n + 1))) = some a := by
  intro n
  induction n with
  | zero =>
      intro vertices a ha
      obtain ⟨x,y,hxy⟩ := S.realized a
      let point : ∀ p : Fin 2, X (D.vertexSort (vertices p)) :=
        Fin.cases x (Fin.cases y (fun r => Fin.elim0 r))
      refine ⟨point, ?_, hxy⟩
      intro p
      have hp : p = 0 := Fin.eq_zero p
      subst p
      exact ⟨a, ha, hxy⟩
  | succ n ih =>
      intro vertices a ha
      let tailVertices : Fin (n + 2) ↪ V :=
        ⟨fun p => vertices p.succ, fun _ _ h => (Fin.succ_injective _) (vertices.injective h)⟩
      have hFirst : vertices 0 ≠ vertices (1 : Fin (n + 3)) := by
        intro h
        have hv := congrArg Fin.val (vertices.injective h)
        simp at hv
      have hTail : vertices (1 : Fin (n + 3)) ≠
          vertices (Fin.last (n + 2)) := by
        intro h
        have hv := congrArg Fin.val (vertices.injective h)
        simp at hv
      have hProduct := stable_triangle_support D N hStable hFirst hTail
        (lineEndpointPair vertices).ne ha
      obtain ⟨b, hb, c, hc, x, y, z, hxy, hyz, hxz⟩ := hProduct
      obtain ⟨tailPoint,hTailEdges,hTailColour⟩ := ih tailVertices c hc
      obtain ⟨g,hgSource,hgTarget⟩ :=
        (S.pair_homogeneous_of_homogeneous H)
          (tailPoint 0) y (tailPoint (Fin.last (n + 1))) z
          (hTailColour.trans hyz.symm)
      let point : ∀ p : Fin (n + 3), X (D.vertexSort (vertices p)) :=
        Fin.cases x (fun p => g • tailPoint p)
      refine ⟨point, ?_, ?_⟩
      · intro p
        refine Fin.cases ?_ (fun q => ?_) p
        · refine ⟨b, hb, ?_⟩
          change S.colour x (g • tailPoint 0) = some b
          rw [hgSource]
          exact hxy
        · obtain ⟨d, hd, hColour⟩ := hTailEdges q
          refine ⟨d, hd, ?_⟩
          change S.colour (g • tailPoint q.castSucc)
            (g • tailPoint q.succ) = some d
          rw [S.colourInvariant_of_homogeneous H g]
          exact hColour
      · change S.colour x (g • tailPoint (Fin.last (n + 1))) = some a
        rw [hgTarget]
        exact hxz

end CCO.StrongPC
