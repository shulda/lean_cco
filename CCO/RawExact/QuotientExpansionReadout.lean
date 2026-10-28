import CCO.RawExact.QuotientExpansionDiagram
import CCO.RawExact.WalkColourReconstruction
import CCO.RawExact.WalkColourAtAllIndices

/-!
# Read every original word from a completed quotient expansion

A homomorphism of the actual expanded diagram preserves precisely each
word occurrence's genuine old atomic certificate. Reconstructing its
real trace gives the full RAW word relation at the two marked images.
Taking every listed word recovers each exact menu, including Top menus.
-/

universe u v w

namespace CCO.RawExact.QuotientExpansion

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {n : Nat} (sort : Fin n → ι) (P : Menus S sort)
variable (hNonempty : ∀ e, TRel.Nonempty (evaluate S (P e)))

/-- The actual source point at every diversity position of one word. -/
def homTrace (f : DiagramHom (diagram S sort P hNonempty))
    (o : Occurrence S sort P) : List (Sigma X) :=
  List.ofFn (fun p : PathPosition S (word S sort P o) =>
    (⟨vertexSort S sort P (atPosition S sort P o p),
      f.point (atPosition S sort P o p)⟩ : Sigma X))

theorem homTrace_length (f : DiagramHom (diagram S sort P hNonempty))
    (o : Occurrence S sort P) :
    (homTrace S sort P hNonempty f o).length = diversityLength S (word S sort P o) + 1 := by
  simp [homTrace]

theorem homTrace_sorts (f : DiagramHom (diagram S sort P hNonempty))
    (o : Occurrence S sort P) :
    (homTrace S sort P hNonempty f o).map Sigma.fst = wordSortTrace S (word S sort P o) := by
  rw [homTrace, List.map_ofFn]
  simp only [Function.comp_def]
  simp_rw [at_sort]
  apply List.ext_getElem
  · simp only [List.length_ofFn, wordSortTrace_length]
  · intro k hk hk'
    simp only [List.getElem_ofFn, pathSortAt, List.get_eq_getElem]

theorem hom_forward_colour (f : DiagramHom (diagram S sort P hNonempty))
    (o : Occurrence S sort P) (p q : PathPosition S (word S sort P o))
    (hpq : p.val + 1 = q.val) :
    taggedColour S
      (⟨vertexSort S sort P (atPosition S sort P o p), f.point (atPosition S sort P o p)⟩ : Sigma X)
      (⟨vertexSort S sort P (atPosition S sort P o q), f.point (atPosition S sort P o q)⟩ : Sigma X) =
      taggedColour S (referencePoint S sort P hNonempty o p)
        (referencePoint S sort P hNonempty o q) := by
  have hAdj : pathAdjacent S (word S sort P o) p q := Or.inl hpq
  have hNe : atPosition S sort P o p ≠ atPosition S sort P o q :=
    (at_injective S sort P o).ne (pathAdjacent_ne S _ p q hAdj)
  obtain ⟨a, ha⟩ := genuineEdge_tagged_some_at_sorts S
    (referencePoint S sort P hNonempty o p) (referencePoint S sort P hNonempty o q)
    (vertexSort S sort P (atPosition S sort P o p))
    (vertexSort S sort P (atPosition S sort P o q))
    (referencePoint_sort S sort P hNonempty o p)
    (referencePoint_sort S sort P hNonempty o q)
    (referencePoint_genuine S sort P hNonempty o p q hAdj)
  have hEdge := (diagram_edge_iff S sort P hNonempty _ _ hNe a).mpr
    ⟨o, p, q, hAdj, rfl, rfl, ha⟩
  have hColour := f.preserves_edge _ _ hNe a hEdge
  have hEncoded := congrArg (fun c : Option (S.Atom
      (vertexSort S sort P (atPosition S sort P o p))
      (vertexSort S sort P (atPosition S sort P o q))) =>
    (⟨vertexSort S sort P (atPosition S sort P o p),
      vertexSort S sort P (atPosition S sort P o q), c⟩ :
        Σ i : ι, Σ j : ι, Option (S.Atom i j))) hColour
  exact hEncoded.trans ha.symm

theorem homTrace_colours (f : DiagramHom (diagram S sort P hNonempty))
    (o : Occurrence S sort P) :
    SameEdgeColours S (realWalkTrace S (referenceWalk S sort P hNonempty o))
      (homTrace S sort P hNonempty f o) := by
  have hLength : (realWalkTrace S (referenceWalk S sort P hNonempty o)).length =
      (homTrace S sort P hNonempty f o).length :=
    (realWalkTrace_length S _).trans (homTrace_length S sort P hNonempty f o).symm
  apply sameEdgeColours_of_indexed S _ _ hLength
  intro k hk hk'
  have hBound : k + 1 < diversityLength S (word S sort P o) + 1 := by
    rwa [realWalkTrace_length S] at hk
  let p : PathPosition S (word S sort P o) := ⟨k, by omega⟩
  let q : PathPosition S (word S sort P o) := ⟨k + 1, hBound⟩
  have h := hom_forward_colour S sort P hNonempty f o p q rfl
  simpa only [referencePoint, wordPathPointAt, List.get_eq_getElem, p, q,
    homTrace, List.getElem_ofFn] using h.symm

/-- The completed source diagram satisfies the original equality-inclusive
word, retaining possible diagonal outputs of positive words. -/
theorem hom_word_relation (f : DiagramHom (diagram S sort P hNonempty))
    (o : Occurrence S sort P) (hPositive : 0 < diversityLength S (word S sort P o)) :
    RawWord.relation S (word S sort P o)
      (f.point (mark S sort P (left o.1))) (f.point (mark S sort P (right o.1))) := by
  obtain ⟨x, y, path, hTrace⟩ := wordPath_of_same_real_trace_colours S
    (word S sort P o) (referenceWalk S sort P hNonempty o)
    (homTrace S sort P hNonempty f o)
    (homTrace_sorts S sort P hNonempty f o)
    (homTrace_colours S sort P hNonempty f o)
  have hStart := realWalkTrace_first_tagged S path
  rw [hTrace, List.getElem?_eq_getElem (by rw [homTrace_length]; omega)] at hStart
  have hStartPoint :
      (homTrace S sort P hNonempty f o)[0]'(by rw [homTrace_length]; omega) =
        (⟨sort (left o.1), f.point (mark S sort P (left o.1))⟩ : Sigma X) := by
    have hPosition : (⟨0, by omega⟩ : PathPosition S (word S sort P o)) =
        pathStart S (word S sort P o) := rfl
    simp only [homTrace, List.getElem_ofFn]
    rw [hPosition, at_start]
    rfl
  have hxTag := (Option.some.inj hStart).symm.trans hStartPoint
  have hx : x = f.point (mark S sort P (left o.1)) := eq_of_heq (Sigma.mk.inj hxTag).2
  have hFinish := realWalkTrace_last_tagged S path
  rw [hTrace, List.getElem?_eq_getElem (by rw [homTrace_length]; omega)] at hFinish
  have hFinishPoint :
      (homTrace S sort P hNonempty f o)[diversityLength S (word S sort P o)]'(by
        rw [homTrace_length]; omega) =
        (⟨sort (right o.1), f.point (mark S sort P (right o.1))⟩ : Sigma X) := by
    simp only [homTrace, List.getElem_ofFn]
    have hPosition : (⟨diversityLength S (word S sort P o), by omega⟩ :
        PathPosition S (word S sort P o)) = pathFinish S (word S sort P o) := rfl
    rw [hPosition, at_finish S sort P o hPositive]
    rfl
  have hyTag := (Option.some.inj hFinish).symm.trans hFinishPoint
  have hy : y = f.point (mark S sort P (right o.1)) := eq_of_heq (Sigma.mk.inj hyTag).2
  have hRelation := (wordPath_iff_relation S (word S sort P o) x y).mp ⟨path⟩
  simpa only [hx, hy] using hRelation

/-- All exact menus are recovered simultaneously from the one completed
source homomorphism. Empty menus impose no path or extra condition. -/
theorem hom_all_menus (f : DiagramHom (diagram S sort P hNonempty))
    (hPositive : ∀ o, 0 < diversityLength S (word S sort P o)) :
    ∀ e, evaluate S (P e)
      (f.point (mark S sort P (left e))) (f.point (mark S sort P (right e))) := by
  intro e w hw
  obtain ⟨slot, hSlot⟩ := List.get_of_mem hw
  have h := hom_word_relation S sort P hNonempty f ⟨e, slot⟩ (hPositive ⟨e, slot⟩)
  simpa only [word, hSlot] using h

end CCO.RawExact.QuotientExpansion
