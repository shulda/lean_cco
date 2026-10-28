import CCO.ParityHasse.Sparse.Statements
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Push

/-!
# The unlabelled connected extraction

A graph with no proper q-colouring has a component with the same
property: proper colourings on all components would assemble to a proper
colouring on the whole graph. Restriction to that induced component
preserves the absence of short cycles. This is solely the unlabelled
(r = 1) step; no labelled sparsity property is claimed to survive.
-/

namespace CCO.ParityHasse.Sparse

variable {V W : Type*}

/-- Absence of short cycles passes through an injective graph homomorphism. -/
theorem noShortCycles_of_injective_hom {G : SimpleGraph V} {H : SimpleGraph W}
    {g : ℕ} (hG : NoShortCycles G g) (f : H →g G) (hf : Function.Injective f) :
    NoShortCycles H g := by
  intro ℓ hℓ hbound e hcycle
  let e' : Fin ℓ ↪ V := ⟨fun p => f (e p), hf.comp e.injective⟩
  exact hG ℓ hℓ hbound e' (fun p => f.map_rel (hcycle p))

/-- If every component admitted a proper q-colouring, their colourings
would combine. Therefore an actual component retains non-colourability. -/
theorem exists_monochromatic_component (G : SimpleGraph V) (q : ℕ)
    (hG : ∀ κ : V → Fin q, ∃ x y, G.Adj x y ∧ κ x = κ y) :
    ∃ C : G.ConnectedComponent,
      ∀ κ : C → Fin q, ∃ x y, C.toSimpleGraph.Adj x y ∧ κ x = κ y := by
  classical
  by_contra h
  push Not at h
  choose κ hκ using h
  let fC : (C : G.ConnectedComponent) → C.toSimpleGraph →g SimpleGraph.completeGraph (Fin q) :=
    fun C => { toFun := κ C, map_rel' := fun hadj => hκ C _ _ hadj }
  let f : G →g SimpleGraph.completeGraph (Fin q) := G.homOfConnectedComponents fC
  obtain ⟨x, y, hxy, heq⟩ := hG f
  exact f.map_rel hxy heq

/-- The finite connected witness consumed by the orbital parity proof. -/
structure ConnectedHighGirthChromatic (q g : ℕ) extends HighGirthChromatic q g where
  connected : graph.Connected

/-- C05: extract an actual finite connected graph of girth > g that
still has no proper q-colouring. No positivity hypothesis on q is needed. -/
noncomputable def HighGirthChromatic.connectedExtraction {q g : ℕ}
    (W : HighGirthChromatic q g) : ConnectedHighGirthChromatic q g := by
  classical
  let h := exists_monochromatic_component W.graph q W.monochromatic
  let C := Classical.choose h
  have hC := Classical.choose_spec h
  letI : Fintype C := Fintype.ofFinite C
  let H := C.toSimpleGraph.overFin (rfl : Fintype.card C = Fintype.card C)
  let e : C.toSimpleGraph ≃g H := C.toSimpleGraph.overFinIso rfl
  refine ⟨⟨Fintype.card C, H, ?_, ?_⟩, ?_⟩
  · have hcomp : NoShortCycles C.toSimpleGraph g :=
      noShortCycles_of_injective_hom W.noShortCycles C.toSimpleGraph_hom Subtype.val_injective
    exact noShortCycles_of_injective_hom hcomp e.symm.toHom e.symm.injective
  · intro κ
    obtain ⟨x, y, hxy, heq⟩ := hC (fun v => κ (e v))
    exact ⟨e x, e y, e.toHom.map_rel hxy, heq⟩
  · exact e.connected_iff.mp C.connected_toSimpleGraph

end CCO.ParityHasse.Sparse
