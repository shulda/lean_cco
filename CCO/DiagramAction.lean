import CCO.ActionBridge

/-!
# Equivariance of actual finite diversity-diagram homomorphisms

A *single* original-source automorphism acts on all vertex images
simultaneously. This elementary lemma is distinct from B001's harder
one-vertex collision-removal operation; in particular it does not
assume homomorphic CCO or SAP.
-/

universe u v w

namespace CCO.DiagramHom

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource ι X} {V : Type w}
variable {D : PartialDiagram S V}
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Composition of a finite specified diversity-diagram homomorphism
with an old sort- and fine-colour-preserving automorphism. -/
def transport (H : HomogeneousSource S G) (g : G)
    (f : DiagramHom D) : DiagramHom D where
  point := fun v => g • f.point v
  preserves_edge := by
    intro x y hxy a ha
    have h := S.colourInvariant_of_homogeneous H
      (i := D.vertexSort x) (j := D.vertexSort y) g
      (f.point x) (f.point y)
    change S.colour (g • f.point x) (g • f.point y) = some a
    exact h.trans (f.preserves_edge x y hxy a ha)

/-- The tagged image is acted on by the same real-universe action; this
is why named sorts cannot accidentally be identified by a transport. -/
theorem transport_image (H : HomogeneousSource S G) (g : G)
    (f : DiagramHom D) (x : V) :
    (transport H g f).image x = g • f.image x := by
  rfl

/-- A simultaneous old automorphism cannot introduce or remove
collisions between distinct formal vertices. The hard B001 repair
therefore needs vertexwise moves, not just this transport. -/
theorem transport_injective (H : HomogeneousSource S G) (g : G)
    (f : DiagramHom D) (hf : f.IsInjective) :
    (transport H g f).IsInjective := by
  intro x y hxy
  have h : g • f.image x = g • f.image y := by
    simpa only [transport_image] using hxy
  have hi := congrArg (fun p : Sigma X => g⁻¹ • p) h
  apply hf
  simpa only [inv_smul_smul] using hi

end CCO.DiagramHom
