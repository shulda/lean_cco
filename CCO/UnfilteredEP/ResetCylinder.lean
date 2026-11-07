import CCO.UnfilteredEP.ResetMidpoint
import CCO.APRamseyReadout.CoordinateBridge
import CCO.HiddenSAPReadings.OrbitalNamedTerms

/-! One source reset orbital is ONE EXISTING complete named semantic
cylinder. It is not added as a new relation or a union of cylinder names.
This supplies the literal relation name used by actual reset tasks. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ParityHasse.Original
open CCO.UnaryTermsReturn CCO.TransitionClosure CCO.TerminalLattice
noncomputable section

section Reading
variable {κ : Type u} {Y : κ → Type v} (S : AtomicSource.{u,v,w} κ Y)
variable {G : Type*} [Group G] [∀ i, MulAction G (Y i)] (H : HomogeneousSource S G)

def completedReadingValue : OriginalCompletedNamedCarrier S H → OriginalNormalCodeTargetValue S
  | .inl ⟨i,x⟩ => ⟨i,⟨⊥,Quotient.mk (⊥ : ColourEq S i).val x⟩⟩
  | .inr q => q.val

theorem completedReadingValue_spec {x : OriginalCompletedNamedCarrier S H}
    {C : OriginalCompletedCoordinateCode S H}
    {q : Quotient (originalCompletedCoordinateKernel S H C).val}
    (h : OriginalCompletedCoordinateReading S H x C q) :
    completedReadingValue S H x = ⟨C.1,⟨originalCompletedCoordinateKernel S H C,q⟩⟩ := by
  cases h <;> rfl

end Reading

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable {i : B.Sorts} (J : FullCloneProperMI B.source i) (m : ActualResetMenu B J)

def resetCylinderPalette : (cloneSource B).Menu i i :=
  (original_named_hidden_pair_cylinder_unique (cloneSource B) (HF B) (cloneSAP B)
    (namedCoordinateHF B ht i J) (namedCoordinateHF B ht i J)
    (Quotient.mk J.val.val m.first) (Quotient.mk J.val.val m.second)).choose

theorem resetCylinderPalette_member :
    resetCylinderPalette B ht J m ∈ originalTypedCylinderNames (cloneSource B) J.val J.val :=
  (original_named_hidden_pair_cylinder_unique (cloneSource B) (HF B) (cloneSAP B)
    (namedCoordinateHF B ht i J) (namedCoordinateHF B ht i J)
    (Quotient.mk J.val.val m.first) (Quotient.mk J.val.val m.second)).choose_spec.1.1

theorem resetCylinderPalette_realized :
    originalTypedCylinderSemanticRelation (cloneSource B) J.val J.val
      (resetCylinderPalette B ht J m)
      (Quotient.mk J.val.val m.first) (Quotient.mk J.val.val m.second) :=
  (original_named_hidden_pair_cylinder_unique (cloneSource B) (HF B) (cloneSAP B)
    (namedCoordinateHF B ht i J) (namedCoordinateHF B ht i J)
    (Quotient.mk J.val.val m.first) (Quotient.mk J.val.val m.second)).choose_spec.1.2

theorem resetCylinderPalette_semantics (q t : Quotient J.val.val) :
    originalTypedCylinderSemanticRelation (cloneSource B) J.val J.val
      (resetCylinderPalette B ht J m) q t ↔ m.relation q t := by
  have h := CCO.HiddenSAPReadings.semantic_cylinder_is_one_orbital
    (cloneSource B) (HF B) J.val J.val (resetCylinderPalette B ht J m)
    (resetCylinderPalette_member B ht J m)
    (Quotient.mk J.val.val m.first) (Quotient.mk J.val.val m.second)
    (resetCylinderPalette_realized B ht J m)
  exact Iff.of_eq (congrFun (congrFun h q) t)

def resetCylinderName : OriginalCompletedCylinderBinaryName (cloneSource B) (HF B) :=
  ⟨⟨i,.inr (namedCoordinateHF B ht i J)⟩,
    ⟨i,.inr (namedCoordinateHF B ht i J)⟩,
      ⟨resetCylinderPalette B ht J m,resetCylinderPalette_member B ht J m⟩⟩

/-- The complete actual predicate includes literal vertex diversity;
the reset orbital itself supplies this condition by irreflexivity. -/
theorem resetCylinderName_iff (q t : Quotient J.val.val) :
    originalCompletedCylinderBinaryPredicate (cloneSource B) (HF B)
      (resetCylinderName B ht J m) (coordinateNode B ht J q) (coordinateNode B ht J t) ↔
        m.relation q t := by
  constructor
  · rintro ⟨_,q',t',hq,ht',hs⟩
    have hq' : q' = q := by
      have hc := completedReadingValue_spec (cloneSource B) (HF B) hq
      change (⟨i,⟨J.val,q⟩⟩ : OriginalNormalCodeTargetValue (cloneSource B)) =
        ⟨i,⟨J.val,q'⟩⟩ at hc
      have hqq' : q = q' := by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hc
      exact hqq'.symm
    have ht'' : t' = t := by
      have hc := completedReadingValue_spec (cloneSource B) (HF B) ht'
      change (⟨i,⟨J.val,t⟩⟩ : OriginalNormalCodeTargetValue (cloneSource B)) =
        ⟨i,⟨J.val,t'⟩⟩ at hc
      have htt' : t = t' := by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hc
      exact htt'.symm
    subst q'
    subst t'
    exact (resetCylinderPalette_semantics B ht J m q t).mp hs
  · intro h
    have hreadq : OriginalCompletedCoordinateReading (cloneSource B) (HF B)
        (coordinateNode B ht J q) ⟨i,.inr (namedCoordinateHF B ht i J)⟩ q :=
      OriginalCompletedCoordinateReading.hidden (S := cloneSource B) (H := HF B)
        (G := ResetGroup B) (namedCoordinateHF B ht i J) q
    have hreadt : OriginalCompletedCoordinateReading (cloneSource B) (HF B)
        (coordinateNode B ht J t) ⟨i,.inr (namedCoordinateHF B ht i J)⟩ t :=
      OriginalCompletedCoordinateReading.hidden (S := cloneSource B) (H := HF B)
        (G := ResetGroup B) (namedCoordinateHF B ht i J) t
    refine ⟨?_,q,t,hreadq,hreadt,
      (resetCylinderPalette_semantics B ht J m q t).mpr h⟩
    intro he
    have hqt : q = t := (namedNode_injective B (namedCoordinateHF B ht i J)) he
    subst t
    exact m.irreflexive q h

end
end CCO.UnfilteredEP
