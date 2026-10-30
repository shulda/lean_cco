import Mathlib.Logic.Function.Defs

/-! The fixed-expanded-source convention for EP.  These are logical assembly
lemmas, not substitutes for the concrete old-root closure and same-host
constructions.  The latter must produce the displayed extension/factorization
and legal restriction maps before these lemmas apply. -/

universe u v w u' v' w'
namespace CCO.FullCode

structure ExpansionFamily where
  Object : Type u
  Expansion : Object → Type v
  Embedding : {A B : Object} → Expansion A → Expansion B → Type w

namespace ExpansionFamily

variable (H : ExpansionFamily.{u,v,w})

/-- One old host works for every allowed expansion, for one fixed expanded
source.  Neither the host nor the source expansion depends on its competitor. -/
def Witness {A : H.Object} (a : H.Expansion A) (B : H.Object) : Prop :=
  ∀ b : H.Expansion B, Nonempty (H.Embedding a b)

def EP : Prop :=
  ∀ (A : H.Object) (a : H.Expansion A), ∃ B : H.Object, H.Witness a B

variable {H}

/-- C49--C50's quantifier step.  Reasonableness extends the *given* expansion
of the normalized old host.  Factoring the whole source embedding through
that actual expanded inclusion then transfers the EP-witness property.  The
concrete full-code proof establishes `factor` from old-root generation. -/
theorem witness_of_reasonable_normalization
    {A D D₀ : H.Object} (a : H.Expansion A)
    (witness : H.Witness a D)
    (Inclusion : H.Expansion D₀ → H.Expansion D → Type w)
    (reasonable : ∀ d₀ : H.Expansion D₀,
      ∃ d : H.Expansion D, Nonempty (Inclusion d₀ d))
    (factor : ∀ (d₀ : H.Expansion D₀) (d : H.Expansion D),
      Inclusion d₀ d → H.Embedding a d → H.Embedding a d₀) :
    H.Witness a D₀ := by
  intro d₀
  obtain ⟨d, ⟨j⟩⟩ := reasonable d₀
  obtain ⟨f⟩ := witness d
  exact ⟨factor d₀ d j f⟩

variable (V : ExpansionFamily.{u',v',w'})

/-- A fully specified route through one fixed hidden old host and one fixed
visible old host.  `restrictedExpansion` must already be legal in the expanded
language: ordinary old heredity alone cannot construct it when new functions
are present.  Actual old-root support/reduct commutation supplies that step. -/
structure FixedHostRoute {A : H.Object} (a : H.Expansion A)
    {X : V.Object} (x : V.Expansion X) (D₀ : H.Object) (B : V.Object) where
  hiddenHost : H.Object
  liftedExpansion : V.Expansion B → H.Expansion hiddenHost
  restrictedExpansion : (b : V.Expansion B) → H.Expansion D₀
  inclusion : (b : V.Expansion B) →
    H.Embedding (restrictedExpansion b) (liftedExpansion b)
  compose : (b : V.Expansion B) → H.Embedding a (restrictedExpansion b) →
    H.Embedding a (liftedExpansion b)
  readRoots : (b : V.Expansion B) → H.Embedding a (liftedExpansion b) →
    V.Embedding x b

/-- C34--C38 after the concrete cofinal host, same-host lift, old-root
expanded closure, restriction and reverse-FCODE constructions have been
performed.  The visible host is fixed before any competing expansion. -/
theorem witness_of_fixed_host_route
    {A : H.Object} {a : H.Expansion A} {X : V.Object} {x : V.Expansion X}
    {D₀ : H.Object} {B : V.Object} (witness : H.Witness a D₀)
    (route : FixedHostRoute V a x D₀ B) : V.Witness x B := by
  intro b
  obtain ⟨f⟩ := witness (route.restrictedExpansion b)
  exact ⟨route.readRoots b (route.compose b f)⟩

/-- Exact-source EP assembly.  This elementary lemma records the dependency
order only.  In a concrete application `prepare` is proved using old-root
normalization and the four full-code contracts; it is not a new hypothesis
of the ambient full-code corollary. -/
theorem ep_of_hidden_ep
    (hiddenEP : H.EP)
    (support : (X : V.Object) → V.Expansion X → H.Object)
    (supportExpansion : (X : V.Object) → (x : V.Expansion X) →
      H.Expansion (support X x))
    (prepare : ∀ (X : V.Object) (x : V.Expansion X) (D : H.Object),
      H.Witness (supportExpansion X x) D →
      ∃ (D₀ : H.Object) (B : V.Object),
        H.Witness (supportExpansion X x) D₀ ∧
        Nonempty (FixedHostRoute V (supportExpansion X x) x D₀ B)) :
    V.EP := by
  intro X x
  obtain ⟨D, hD⟩ := hiddenEP (support X x) (supportExpansion X x)
  obtain ⟨D₀, B, hD₀, ⟨route⟩⟩ := prepare X x D hD
  exact ⟨B, witness_of_fixed_host_route V hD₀ route⟩

end ExpansionFamily
end CCO.FullCode
