import CCO.RigidGroupoid.Geometry.Source

/-! Downstream actual-source consumers, including true equality, zero-length
quotient words and the positive own-gate instance discharging A05. Mixed-sort
bridge correspondence keeps the whole assigned middle kernel consistently. -/

universe u v w t
namespace CCO.RigidGroupoid.Geometry
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def identityKernel (i : ι) : Kernel S i := ⟨⊥,fullExact_identity S i⟩

theorem identity_arrow_real_equality (i : ι) :
    (Arrow.id (identityKernel S i)).rel = TRel.ident X i := rfl

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)

theorem empty_quotient_word_pullback (F : ∀ i, Kernel S i) (i : ι) :
    GroupActions.pullback (Canonical.projection F i) (Canonical.projection F i)
      (RawWord.relation (Canonical.source H F) (.nil i)) = (F i).rel :=
  (Canonical.kernel_words F i).trans (Canonical.words_relation F i)

noncomputable def actual_own_gate_correspondence (F : ∀ i, Kernel S i) :=
  Canonical.ownGateGroupoidIso H cco F

theorem own_gate_is_true_quotient_equality (F : ∀ i, Kernel S i) (i : ι) :
    (Canonical.gates H F F (fun _ => le_rfl) (Canonical.own_projected_exact H F) i).rel =
      TRel.ident (Canonical.Carrier F) i := Canonical.own_gate_relation F i

theorem actual_bridge_readout (F A : ∀ i, Kernel S i) (hFA : ∀ i, F i ≤ A i)
    (hProjected : ∀ i, FullExact (Canonical.source H F)
      ((A i).projectedSetoid (Canonical.projection F i) (Canonical.onto F i)
        (Canonical.nested F A hFA i)).r)
    {i j : ι} (R : Arrow S (A i) (A j)) :
    ((Canonical.bridgeGroupoidIso H cco F A hFA hProjected).homEquiv i j R).rel =
      Quotient.image (Canonical.projection F i) (Canonical.projection F j) R.rel := rfl

/-- Endpoint-only C16 consumer: the independently quotiented language may
have other sorts, whose COARSE projected gates are not premises here. -/
theorem endpoint_bridge_readout (F : ∀ i, Kernel S i) {i j : ι}
    (A : Kernel S i) (B : Kernel S j) (ha : F i ≤ A) (hb : F j ≤ B)
    (hAq : FullExact (Canonical.source H F)
      (A.projectedSetoid (Canonical.projection F i) (Canonical.onto F i)
        (Canonical.endpointNested F A ha)).r)
    (hBq : FullExact (Canonical.source H F)
      (B.projectedSetoid (Canonical.projection F j) (Canonical.onto F j)
        (Canonical.endpointNested F B hb)).r)
    (R : Arrow S A B) :
    ((Canonical.endpointArrowEquiv H cco F A B ha hb hAq hBq) R).rel =
      Quotient.image (Canonical.projection F i) (Canonical.projection F j) R.rel := rfl

/-- A genuine interval/transport consumer of the standing source, retaining
the original dominance premise and never replacing it with quotient dominance.
-/
theorem original_dominant_consumer {i j : ι} {A : Kernel S i} {B : Kernel S j}
    (t : Arrow S A A) (ht : t ≠ Arrow.id A) (hd : Dominant A t) (R : Arrow S A B) :
    let C := exactCalculus_of_homogeneous_CCO S H cco
    transport C t R ≠ Arrow.id B ∧
      (transport C t R).comp C (transport C t R) = Arrow.id B ∧
      Dominant B (transport C t R) ∧
      (∀ T : Arrow S A B, transport C t T = transport C t R) ∧
      ∀ q : B.Class, (transport C t R).quotientMap H q ≠ q :=
  transport_source_consumer (exactCalculus_of_homogeneous_CCO S H cco) H t ht hd R

end CCO.RigidGroupoid.Geometry
