import CCO.HKNReservoir.RequestSaturation
import CCO.HKNReservoir.DistinguishedNormalization
import AllThoseEPPA.MainTheorems

/-! The two version-pinned external theorems are applied in order. The
unrestricted outputs acquire no packet or functionality assumptions here;
those are recovered separately from actual irreducible faithfulness. -/
universe u v w t
namespace CCO.HKNReservoir
open AllThoseEPPA
noncomputable section
variable {L : Language.{u}} [L.HasUnaryFunctions] {Γ : Type w} [Group Γ]
variable (act : L.Action Γ) {α : Type (max u v)}

/-- Both finite stages retain literal copies of the SAME source, exact
language components and the full closed-vertex local-tree condition. -/
structure StagedWitness (A : Structure L α) (n : ℕ) where
  FirstNew : Type (max u v)
  finiteFirstNew : Finite FirstNew
  first : Structure L (α ⊕ FirstNew)
  firstCopy : Structure.Embedding act A first
  firstCopy_lang : firstCopy.lang = 1
  firstCopy_apply : ∀ x, firstCopy x = Sum.inl x
  firstEPPA : Structure.IsEPPAWitness act firstCopy
  firstFaithful : Structure.IsIrreducibleStructureFaithful act firstCopy
  New : Type (max u v)
  finiteNew : Finite New
  model : Structure L (α ⊕ New)
  inclusion : Structure.Embedding act A model
  inclusion_lang : inclusion.lang = 1
  inclusion_apply : ∀ x, inclusion x = Sum.inl x
  eppa : Structure.IsEPPAWitness act inclusion
  faithful : Structure.IsIrreducibleStructureFaithful act inclusion
  back : Structure.Homomorphism act model first
  backEmbedding : Structure.Homomorphism.IsHomomorphismEmbedding act back
  localTrees : DistinguishedNormalization.LocalTrees act A model n

/-- E01 followed by E02, with ONE global distinguished normalization
at EACH stage. Finite Gamma explicitly discharges the relabel orbit. -/
theorem staged_witness [Finite α] [Finite Γ] (A : Structure L α) (n : ℕ) :
    Nonempty (StagedWitness act A n) := by
  have hOrbit : A.HasFiniteRelabelOrbit act := Set.finite_range _
  obtain ⟨δ,hδ,W,ψ,hCoherent,hFaithful⟩ := MainTheorems.unrestrictedFaithfulCoherentEPPA act A hOrbit
  letI := hδ
  have hEPPA : Structure.IsEPPAWitness act ψ := hCoherent.some.isEPPAWitness
  let first := DistinguishedNormalization.model ψ
  let firstCopy := DistinguishedNormalization.inclusion ψ
  have firstEPPA : Structure.IsEPPAWitness act firstCopy := DistinguishedNormalization.normalizedEPPA ψ hEPPA
  obtain ⟨ε,hε,B,ι,hep,hfaith,⟨f,hf⟩,hSmall,_⟩ :=
    MainTheorems.restrictedLocallyTreeLikeEPPA act A first firstCopy firstEPPA n
  letI := hε
  have hTrees : DistinguishedNormalization.LocalTrees act A B n := by
    intro S hS hBound
    obtain ⟨U,T,hT,g,hg⟩ := hSmall S hS hBound
    exact ⟨U,T,⟨TreePresentation.ofTree hT⟩,g,hg⟩
  exact ⟨{
    FirstNew := DistinguishedNormalization.New ψ
    finiteFirstNew := inferInstance
    first := first
    firstCopy := firstCopy
    firstCopy_lang := rfl
    firstCopy_apply := fun _ => rfl
    firstEPPA := firstEPPA
    firstFaithful := DistinguishedNormalization.normalizedFaithful ψ hFaithful
    New := DistinguishedNormalization.New ι
    finiteNew := inferInstance
    model := DistinguishedNormalization.model ι
    inclusion := DistinguishedNormalization.inclusion ι
    inclusion_lang := rfl
    inclusion_apply := fun _ => rfl
    eppa := DistinguishedNormalization.normalizedEPPA ι hep
    faithful := DistinguishedNormalization.normalizedFaithful ι hfaith
    back := DistinguishedNormalization.transportBackmap (DistinguishedNormalization.iso ι) (DistinguishedNormalization.iso_surjective ι) f
    backEmbedding := DistinguishedNormalization.transportBackmap_homomorphismEmbedding (DistinguishedNormalization.iso ι) (DistinguishedNormalization.iso_surjective ι) f hf
    localTrees := DistinguishedNormalization.normalizedLocalTrees ι hTrees }⟩

/-- Every partial request, including all empty-domain language choices,
extends with the EXACT requested component after normalization. -/
theorem StagedWitness.exact_extensions {A : Structure L α} {n : ℕ} (W : StagedWitness act A n)
    (p : Structure.PartialAutomorphism act A) :
    ∃ g : Structure.Automorphism act W.model, g.lang = p.lang ∧
      ∀ x, x ∈ p.source → g (Sum.inl x) = Sum.inl (p x) := by
  obtain ⟨g,hg⟩ := W.eppa p
  refine ⟨g,?_,?_⟩
  · simpa only [W.inclusion_lang,mul_one,one_mul] using hg.1
  · intro x hx
    simpa only [W.inclusion_apply] using hg.2 x hx

section ActualSource
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))

/-- HKN's threshold counts ACTUAL vertices in b whole packets. -/
def packetThreshold (b : ℕ) : ℕ := b * Nat.card (ResidualData.PacketGroup S H)

include R in
theorem packetThreshold_pos (b : ℕ) (hb : 3 ≤ b) : 0 < packetThreshold S H b := by
  letI := translation_finite S (finitePacket S H) H (R.packet_thin S H)
  have hk : 0 < Nat.card (ResidualData.PacketGroup S H) := Nat.card_pos_iff.mpr ⟨inferInstance,inferInstance⟩
  exact Nat.mul_pos (lt_of_lt_of_le (by decide : 0<3) hb) hk

/-- Actual source hypotheses, finite orbit, irreducibility and threshold
are all discharged before applying the two external theorems. -/
theorem actual_staged_witness (A : Set (SourceCarrier S H R B))
    (hA : (sourceStructure S H R B hB).IsClosed A) [Finite A] (b : ℕ) (hb : 3 ≤ b) :
    (encode (finiteSourceData S H R B hB A hA)).IsIrreducible ∧
      0 < packetThreshold S H b ∧
      Nonempty (StagedWitness (sourceAction S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) (packetThreshold S H b)) :=
  ⟨finiteSource_irreducible S H R B hB A hA,packetThreshold_pos S H R b hb,
    staged_witness (sourceAction S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) (packetThreshold S H b)⟩

/-- The normalized witness extends EVERY original compatible request,
after the proved full-packet saturation, with exactly its given gamma. -/
theorem actual_original_request_extensions (A : Set (SourceCarrier S H R B))
    (hA : (sourceStructure S H R B hB).IsClosed A) [Finite A] {n : ℕ}
    (W : StagedWitness (sourceAction S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) n)
    (p : Request (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA)) :
    ∃ g : Structure.Automorphism (sourceAction S H R B Δ) W.model, g.lang = p.lang ∧
      ∀ x, x ∈ p.point.source → g (Sum.inl x) = Sum.inl (p.point x) := by
  obtain ⟨q,hl,hS,_,hext,_⟩ := saturate_request S H R B hB Δ A hA p
  obtain ⟨g,hg,hpoint⟩ := StagedWitness.exact_extensions (sourceAction S H R B Δ) W q
  refine ⟨g,hg.trans hl,?_⟩
  intro x hx
  have h1 (y : A) : (finiteSourceData S H R B hB A hA).move 1 y = y :=
    Subtype.ext (source_move_one S H R B hB y.val)
  have hxq : x ∈ q.source := by
    rw [hS]
    exact subset_saturation _ h1 p.point.source hx
  rw [hpoint x hxq,hext x hx]

/-- Every global language component survives, including components seen
only through empty real domains. -/
theorem all_language_components (A : Set (SourceCarrier S H R B))
    (hA : (sourceStructure S H R B hB).IsClosed A) {n : ℕ}
    (W : StagedWitness (sourceAction S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) n) (γ : Δ) :
    ∃ g : Structure.Automorphism (sourceAction S H R B Δ) W.model, g.lang = γ := by
  obtain ⟨g,hg,_⟩ := StagedWitness.exact_extensions (sourceAction S H R B Δ) W
    (emptyRequest (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA) γ)
  exact ⟨g,hg⟩
end ActualSource

end
end CCO.HKNReservoir
