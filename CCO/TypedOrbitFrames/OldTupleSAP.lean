import CCO.TypedOrbitFrames.ChordHomGlue

/-!
# B053 C04: original-age SAP gluing of arbitrary finite old tuples

An old cycle homomorphism can be noninjective. It is therefore
unsound to invoke old AgeSAP on its formal source cycle as if it
were an induced age object. But every FINITE tuple of actual old
points is the image of an entirely unconstrained old partial
diagram; its ACTUAL finite induced image is a legitimate age
object.

Use the already compiled source11 C03 old SAP bridge on those
actual induced image objects. The resulting maps to ONE genuine
old age member preserve ALL original typed pair colours (not
merely those displayed in the unconstrained auxiliary diagrams)
and agree at both ends of one actual diversity chord.

No quotient-age SAP, hidden homogeneity, extra old source
relationship, or completion of an arbitrary partial source
is introduced.
-/

universe u v w z p t
namespace CCO.TypedOrbitFrames

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A finite actual old tuple represented as an OLD partial
diagram with NO specified edges. It is used only to expose
the tuple's actual induced OLD image to the previous
source-specific C03 AgeSAP theorem. -/
def originalUnconstrainedTupleDiagram {V : Type z}
    [Finite V] (f : V → Sigma X) : PartialDiagram S V where
  finite_type := inferInstance
  vertexSort := fun a => (f a).1
  edge := fun _ _ _ => none
  edge_reverse := by
    intro a b hab c
    simp

/-- The tuple is a genuine homomorphism of its EMPTY-edge
auxiliary diagram. This statement does not introduce
or verify any additional OLD or hidden relation. -/
def originalUnconstrainedTupleHom {V : Type z}
    [Finite V] (f : V → Sigma X) :
    DiagramHom (originalUnconstrainedTupleDiagram S f) where
  point := fun a => (f a).2
  preserves_edge := by
    intro a b hab c hc
    cases hc

/-- A genuine specified original diversity chord in two
finite actual OLD tuples can be aligned and amalgamated.

The old input tuples may identify nonadjacent formal cycle
positions. Every pair colour within each tuple remains
correct after amalgamation; the ONLY distinguished forced
identifications are the two literal chord endpoints. This
is the actual source C03 theorem applied to the full
old induced images, not an arbitrary graph pushout. -/
theorem original_old_tuples_same_chord_sap
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {V : Type z} {W : Type p} [Finite V] [Finite W]
    (f : V → Sigma X) (g : W → Sigma X)
    {i j : ι} (a : S.Atom i j)
    (x x' : X i) (y y' : X j)
    (hxy : S.colour x y = some a)
    (hx'y' : S.colour x' y' = some a)
    (u₀ u₁ : V) (v₀ v₁ : W)
    (hfu₀ : f u₀ = (⟨i,x⟩ : Sigma X))
    (hfu₁ : f u₁ = (⟨j,y⟩ : Sigma X))
    (hgv₀ : g v₀ = (⟨i,x'⟩ : Sigma X))
    (hgv₁ : g v₁ = (⟨j,y'⟩ : Sigma X)) :
    ∃ (M : FiniteInduced (X := X))
      (fl : V → Sigma X) (gr : W → Sigma X),
      (∀ u, fl u ∈ M.vertices) ∧
      (∀ v, gr v ∈ M.vertices) ∧
      (∀ u v, taggedColour S (fl u) (fl v) =
        taggedColour S (f u) (f v)) ∧
      (∀ u v, taggedColour S (gr u) (gr v) =
        taggedColour S (g u) (g v)) ∧
      fl u₀ = gr v₀ ∧ fl u₁ = gr v₁ := by
  let L : PartialDiagram S V := originalUnconstrainedTupleDiagram S f
  let R : PartialDiagram S W := originalUnconstrainedTupleDiagram S g
  let lf : DiagramHom L := originalUnconstrainedTupleHom S f
  let rg : DiagramHom R := originalUnconstrainedTupleHom S g
  have hl₀ : lf.image u₀ = (⟨i,x⟩ : Sigma X) := hfu₀
  have hl₁ : lf.image u₁ = (⟨j,y⟩ : Sigma X) := hfu₁
  have hr₀ : rg.image v₀ = (⟨i,x'⟩ : Sigma X) := hgv₀
  have hr₁ : rg.image v₁ = (⟨j,y'⟩ : Sigma X) := hgv₁
  obtain ⟨M,fl,gr,hMemL,hMemR,hColourL,hColourR,h0,h1⟩ :=
    original_same_chord_hom_images_sap_glue
      S H sap L R lf rg a x x' y y' hxy hx'y'
      u₀ u₁ v₀ v₁ hl₀ hl₁ hr₀ hr₁
  refine ⟨M,fl,gr,hMemL,hMemR,?_,?_,h0,h1⟩
  · intro u v
    exact hColourL u v
  · intro u v
    exact hColourR u v

end CCO.TypedOrbitFrames
