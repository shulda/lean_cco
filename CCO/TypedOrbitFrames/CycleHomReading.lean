import CCO.TypedOrbitFrames.ChordCycleStep
import CCO.Finite

/-!
# B053 C04: recover a genuine typed CycleHom from old side-colour reading

The chord SAP step produces an actual old Sigma-valued map on the
original cycle positions. If each side has precisely the original
complete optional typed colour, each vertex has its prescribed old
sort and these values give a genuine CCO.CycleHom of the literal
CCO.SimpleCycle. No injectivity on the homomorphism is asserted.
-/

namespace CCO.TypedOrbitFrames

universe u v w z
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}

/-- Explicit dependent Sigma transport along equality of old sort labels. -/
private theorem sigma_mk_transport_eta {a b : ι} (hab : a = b) (x : X a) :
    (⟨b, Eq.mp (congrArg X hab) x⟩ : Sigma X) =
      (⟨a,x⟩ : Sigma X) := by
  cases hab
  rfl

/-- The full old pair-colour reading of the specified side at p,
including both original sort tags; its atom is guaranteed present
by the actual SimpleCycle.specified field. -/
def originalSpecifiedCycleSideReading
    {D : PartialDiagram S V} (C : SimpleCycle D)
    (p : Fin C.length) :
    (Σ i : ι, Σ j : ι, Option (S.Atom i j)) :=
  ⟨D.vertexSort (C.vertices p),
   D.vertexSort (C.vertices (CCO.cyclicNext C.length_pos p)),
   D.edge (C.vertices p)
     (C.vertices (CCO.cyclicNext C.length_pos p)) (C.next_ne p)⟩

/-- One Sigma-valued coloured reading, with exact old sorts and
all specified side atoms, is a genuine CycleHom into the SAME
original homogeneous source. -/
theorem original_coloured_side_reading_is_cycle_hom
    {D : PartialDiagram S V} (C : SimpleCycle D)
    (f : Fin C.length → Sigma X)
    (hf : ∀ p : Fin C.length,
      taggedColour S (f p) (f (CCO.cyclicNext C.length_pos p)) =
        originalSpecifiedCycleSideReading S C p) :
    CycleHom C := by
  have hs : ∀ p : Fin C.length,
      (f p).1 = D.vertexSort (C.vertices p) := by
    intro p
    exact congrArg Sigma.fst (hf p)
  let pt : ∀ p : Fin C.length, X (D.vertexSort (C.vertices p)) :=
    fun p => Eq.mp (congrArg X (hs p)) (f p).2
  have htag (p : Fin C.length) :
      (⟨D.vertexSort (C.vertices p),pt p⟩ : Sigma X) = f p := by
    dsimp [pt]
    calc
      (⟨D.vertexSort (C.vertices p),
        Eq.mp (congrArg X (hs p)) (f p).2⟩ : Sigma X) =
          (⟨(f p).1,(f p).2⟩ : Sigma X) :=
            sigma_mk_transport_eta (hs p) (f p).2
      _ = f p := by cases f p; rfl
  refine ⟨pt, ?_⟩
  intro p a ha
  have hc := hf p
  rw [← htag p, ← htag (CCO.cyclicNext C.length_pos p)] at hc
  have hoption :
      S.colour (pt p) (pt (CCO.cyclicNext C.length_pos p)) =
        D.edge (C.vertices p)
          (C.vertices (CCO.cyclicNext C.length_pos p))
          (C.next_ne p) := by
    simpa only [taggedColour, originalSpecifiedCycleSideReading,
      Sigma.mk.injEq, heq_eq_eq, true_and] using hc
  exact hoption.trans ha

end CCO.TypedOrbitFrames
