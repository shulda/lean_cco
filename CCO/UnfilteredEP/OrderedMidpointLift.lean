import CCO.UnfilteredEP.OrderedMidpointSource
import CCO.TerminalHiddenHN.CompletionBridge
import CCO.HiddenSAPReadings.SourceSupport

/-! A whole actual finite-member realization automatically lifts the
ENTIRE generated pair diagram back into that member. No independent
pair-completion or embedding-extension premise is required. -/

universe u v w z
namespace CCO.UnfilteredEP
open APRamseyReadout CloneTupleGeometry UnarySupport
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

theorem realized_cutPair_embedding {V : Type z}
    {C : Structure (Sig B ht) V} (e : C.Embedding (Target B ht))
    (D : HiddenCut B) (q t : Quotient D.2.val.val) (x y : V)
    (hq : e.point x = namedNode B D.2 q) (ht' : e.point y = namedNode B D.2 t) :
    ∃ s : (cutPairStructure B ht D q t).Embedding C,
      s.point (cutPairLeft B ht D q t) = x ∧
      s.point (cutPairRight B ht D q t) = y ∧
      ∀ p, e.point (s.point p) = p.val := by
  have closed := CCO.HiddenSAPReadings.SourceSupport.embedding_range_closed e
  have contained : cutPairSet B ht D q t ⊆ Set.range e.point := by
    apply (Target B ht).closure_minimal closed
    intro p hp
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact ⟨x,hq⟩
    · exact ⟨y,ht'⟩
  let rangeIso := CCO.HiddenSAPReadings.SourceSupport.embedding_image_iso e
  let sub : (cutPairStructure B ht D q t).Embedding
      ((Target B ht).induce (Set.range e.point) closed) := {
    point := fun p => ⟨p.val,contained p.property⟩
    sort_eq := fun _ => rfl
    map_func := fun _ _ _ h => h
    map_rel := fun _ _ h => h
    injective := fun _ _ h => Subtype.ext
      (congrArg (fun a : Set.range e.point => a.val) h)
    reflect_func := fun F p a ha =>
      ⟨⟨a.val,(Target B ht).isClosed_closure _ F p.val p.property ha⟩,ha,rfl⟩
    reflect_rel := fun _ _ h => h }
  let s := TerminalHiddenHN.embedding_comp sub (TerminalHiddenHN.diagramIso_symm rangeIso).toEmbedding
  have law (p) : e.point (s.point p) = p.val := by
    exact congrArg Subtype.val (rangeIso.equiv.apply_symm_apply (sub.point p))
  refine ⟨s,?_,?_,law⟩
  · apply e.injective
    exact (law _).trans hq.symm
  · apply e.injective
    exact (law _).trans ht'.symm

end
end CCO.UnfilteredEP
