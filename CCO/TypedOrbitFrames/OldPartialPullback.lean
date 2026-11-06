import CCO.TypedOrbitFrames.NormalizedChordCycleHom
import CCO.Finite

/-!
# B053 C04: actual finite-index pullback of the original old partial diagram

The source chord-splitting argument must use genuine shorter typed
`PartialDiagram` objects, not fabricated untyped graphs. An injective
reindexing of formal vertices pulls back EVERY actual old named sort,
specified diversity atom, converse, and missing edge LITERALLY.
It never fills in unspecified clone-clone pairs or introduces an
equality diversity atom. An existing old full diagram homomorphism
restricts along this reindexing, without assuming its injectivity
away from genuine old diversity edges.

The chosen subcycle index maps are supplied by the compiled
`originalChordLeftIndex` and `originalChordRightIndex`.
Constructing the `SimpleCycle` records with their actual
closing chord and all source side certificates remains separate.
-/

universe u v w z t
namespace CCO.TypedOrbitFrames

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} {W : Type t}

/-- Exact OLD pullback of an actual typed finite partial diagram
along an injective formal-vertex reindexing, including all
old typed edge colours and precisely the original gaps. -/
def originalOldPullbackDiagram
    (D : PartialDiagram S V)
    [Finite W] (e : W ↪ V) : PartialDiagram S W where
  finite_type := inferInstance
  vertexSort := fun w => D.vertexSort (e w)
  edge := fun x y hxy => D.edge (e x) (e y) (e.injective.ne hxy)
  edge_reverse := by
    intro x y hxy a
    exact D.edge_reverse (e x) (e y) (e.injective.ne hxy) a

/-- The pullback has EXACTLY the original old optional colour
at every distinct ordered source-vertex pair, including
the proper typed endpoint tags. No new constraint is imposed. -/
theorem original_old_pullback_edge_eq
    (D : PartialDiagram S V)
    [Finite W] (e : W ↪ V)
    (x y : W) (hxy : x ≠ y) :
    (originalOldPullbackDiagram S D e).edge x y hxy =
      D.edge (e x) (e y) (e.injective.ne hxy) := rfl

/-- Any REAL old diagram homomorphism restricts along an
injective reindexing of its entire actual typed edge specification.
This is NOT the converse and does not claim arbitrary partial
diagram completability. -/
def originalOldPullbackHom
    (D : PartialDiagram S V)
    [Finite W] (e : W ↪ V)
    (f : DiagramHom D) :
    DiagramHom (originalOldPullbackDiagram S D e) where
  point := fun x => f.point (e x)
  preserves_edge := by
    intro x y hxy a ha
    exact f.preserves_edge (e x) (e y)
      (e.injective.ne hxy) a ha

end CCO.TypedOrbitFrames
