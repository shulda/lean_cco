import CCO.ResetOrder.Generic.Reduct

/-! Relative EP composition with an actual closed-image gate. We construct the
upper restriction on EXACTLY the intermediate carrier, rather than assuming a
categorical lifting oracle. -/
universe u v
namespace CCO.ResetOrder.Generic
variable {S : Type u} {L M N : Language S}

def Object.onCarrier (B : Object.{u,v} L) (d : Structure M B.Carrier) : Object.{u,v} M :=
  ⟨B.Carrier, B.finite, d⟩

structure Expansion (ρ : Reduct L M) (K : Age.{u,v} M) (B : Object.{u,v} L) where
  data : Structure M B.Carrier
  member : K (B.onCarrier data)
  reduct_eq : ρ.data data = B.data

namespace Expansion
variable {ρ : Reduct L M} {K : Age.{u,v} M} {B : Object.{u,v} L}

def object (E : Expansion ρ K B) : Object.{u,v} M := B.onCarrier E.data

theorem reduct_object (E : Expansion ρ K B) : ρ.object E.object = B := by
  change (⟨B.Carrier, B.finite, ρ.data E.data⟩ : Object L) = B
  rw [E.reduct_eq]

end Expansion

def MapsClass (ρ : Reduct L M) (K : Age.{u,v} M) (J : Age.{u,v} L) : Prop :=
  ∀ C, K C → J (ρ.object C)

def ReductSurjective (ρ : Reduct L M) (K : Age.{u,v} M) (J : Age.{u,v} L) : Prop :=
  ∀ B, J B → Nonempty (Expansion ρ K B)

def RelativeEP (ρ : Reduct L M) (K : Age.{u,v} M) (J : Age.{u,v} L) : Prop :=
  ∀ A, K A → ∃ B, J B ∧
    ∀ E : Expansion ρ K B, Nonempty (Object.Embedding A E.object)

/-- A14 in structural form: every intermediate image is upper-function closed. -/
def RestrictionGate (ρ : Reduct L M) (K : Age.{u,v} M) (J : Age.{u,v} L) : Prop :=
  ∀ C, K C → ∀ B, J B → ∀ f : Object.Embedding B (ρ.object C),
    C.data.Closed (Set.range f.point)

/-- The legal upper expansion is constructed by inverse-image interpretations.
Heredity is applied only AFTER closedness has supplied the actual upper embedding. -/
def pullbackExpansion (ρ : Reduct L M) {K : Age.{u,v} M} (hH : Hereditary M K)
    {C : Object.{u,v} M} {B : Object.{u,v} L} (hC : K C)
    (f : Object.Embedding B (ρ.object C))
    (hc : C.data.Closed (Set.range f.point)) : Expansion ρ K B where
  data := C.data.pullback f.point f.injective
  member := hH hC (C.data.pullbackEmbedding f.point f.injective hc)
  reduct_eq := ρ.pullback_reduct_eq f hc

def pullbackEmbedding (ρ : Reduct L M) {K : Age.{u,v} M} (hH : Hereditary M K)
    {C : Object.{u,v} M} {B : Object.{u,v} L} (hC : K C)
    (f : Object.Embedding B (ρ.object C))
    (hc : C.data.Closed (Set.range f.point)) :
    Object.Embedding (pullbackExpansion ρ hH hC f hc).object C :=
  C.data.pullbackEmbedding f.point f.injective hc

theorem relation_only_restrictionGate (ρ : Reduct L M) (hρ : ρ.KeepsFunctions)
    (K : Age.{u,v} M) (J : Age.{u,v} L) : RestrictionGate ρ K J := by
  intro C _ B _ f
  exact ρ.closed_range_of_keepsFunctions hρ f

/-- Choose BOTH hosts before the arbitrary final expansion. -/
theorem foundational_relative_EP_composition (ρ : Reduct L M) (σ : Reduct M N)
    {K0 : Age.{u,v} L} {K1 : Age.{u,v} M} {K2 : Age.{u,v} N}
    (hH2 : Hereditary N K2) (hσ : MapsClass σ K2 K1)
    (gate : RestrictionGate σ K2 K1)
    (h21 : RelativeEP σ K2 K1) (h10 : RelativeEP ρ K1 K0) :
    RelativeEP (ρ.compose σ) K2 K0 := by
  intro A hA
  obtain ⟨B, hB, hAB⟩ := h21 A hA
  obtain ⟨C, hC, hBC⟩ := h10 B hB
  refine ⟨C, hC, ?_⟩
  intro E
  let E1 : Expansion ρ K1 C := {
    data := σ.data E.data
    member := hσ E.object E.member
    reduct_eq := E.reduct_eq }
  obtain ⟨f⟩ := hBC E1
  have hf : Object.Embedding B (σ.object E.object) := f
  have hc : E.object.data.Closed (Set.range hf.point) := gate E.object E.member B hB hf
  let B2 := pullbackExpansion σ hH2 E.member hf hc
  obtain ⟨g⟩ := hAB B2
  exact ⟨(pullbackEmbedding σ hH2 E.member hf hc).compose g⟩

theorem relation_only_relative_EP_composition (ρ : Reduct L M) (σ : Reduct M N)
    {K0 : Age.{u,v} L} {K1 : Age.{u,v} M} {K2 : Age.{u,v} N}
    (hH2 : Hereditary N K2) (hσ : MapsClass σ K2 K1) (hs : σ.KeepsFunctions)
    (h21 : RelativeEP σ K2 K1) (h10 : RelativeEP ρ K1 K0) :
    RelativeEP (ρ.compose σ) K2 K0 :=
  foundational_relative_EP_composition ρ σ hH2 hσ
    (relation_only_restrictionGate σ hs K2 K1) h21 h10

/-- Structural restriction gates compose by TWO actual inherited pullbacks. -/
theorem restrictionGate_compose (ρ : Reduct L M) (σ : Reduct M N)
    {K0 : Age.{u,v} L} {K1 : Age.{u,v} M} {K2 : Age.{u,v} N}
    (hH1 : Hereditary M K1) (hσ : MapsClass σ K2 K1)
    (gρ : RestrictionGate ρ K1 K0) (gσ : RestrictionGate σ K2 K1) :
    RestrictionGate (ρ.compose σ) K2 K0 := by
  intro C hC B hB f
  have hm := hσ C hC
  have hc : (σ.object C).data.Closed (Set.range f.point) := gρ (σ.object C) hm B hB f
  let B1 := pullbackExpansion ρ hH1 hm f hc
  let e := pullbackEmbedding ρ hH1 hm f hc
  have hfull : C.data.Closed (Set.range e.point) := gσ C hC B1.object B1.member e
  exact @hfull

end CCO.ResetOrder.Generic
