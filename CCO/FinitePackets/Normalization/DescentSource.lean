import CCO.FinitePackets.Normalization.PaletteDescent
import CCO.FinitePackets.Geometry.Basic
import CCO.RawExact.CanonicalQuotientInheritance
import CCO.RealClosure.Bounds.SortRestriction

/-!
# Actual source-preserving finite exact quotient steps

Each step below has the literal quotient carrier, the actual quotient orbital
palette, the same original ambient group, and proved source inheritance.
Countability is retained exactly where the accepted joint-lifting provider
needs it. No SAP preservation or choice of a section is asserted.
-/

universe v w t

namespace CCO.FinitePackets.Normalization

open CCO.ParityHasse.Original CCO.FinitePackets.Geometry
open CCO.RawExact

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

/-- An available normalization step is an actual nonidentity finite-class
equivalence with a FULL RAW exact presentation in the CURRENT source. -/
structure FiniteExactKernel where
  kernel : ColourEq S ()
  finite : FiniteIndex S ⊥ kernel
  exact : NonemptyExact S () ()
  represents : evaluate S exact.words = kernel.val.r
  proper : kernel ≠ ⊥

def FiniteExactKernel.data (K : FiniteExactKernel S) :
    CanonicalQuotients.ExactData S ({K.kernel.val} : Finset (Setoid M)) :=
  CanonicalQuotients.singletonData S K.kernel.val K.exact K.represents

abbrev FiniteExactKernel.index (K : FiniteExactKernel S) :=
  CanonicalQuotients.singletonIndex K.kernel.val

variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G)

def exactQuotientAction (K : FiniteExactKernel S) :
    MulAction G (Quotient K.kernel.val) :=
  CanonicalQuotients.action S H K.data K.index

/-- The palette of an actual quotient is in the carrier universe; this
provides a fixed universe for every subsequent step of the finite chain. -/
noncomputable def exactQuotientSource (K : FiniteExactKernel S) :
    AtomicSource.{0,v,v} Unit (fun _ => Quotient K.kernel.val) := by
  letI : ∀ k : CanonicalQuotients.Index ({K.kernel.val} : Finset (Setoid M)),
      MulAction G (CanonicalQuotients.Carrier k) := CanonicalQuotients.action S H K.data
  exact RealClosure.Bounds.sortSource (CanonicalQuotients.source S H K.data) K.index

theorem exactQuotientSource_homogeneous [Countable M]
    (cco : SemanticCCO.{0,v,v,w} S) (K : FiniteExactKernel S) :
    letI := exactQuotientAction S H K
    HomogeneousSource (exactQuotientSource S H K) G := by
  letI : ∀ k : CanonicalQuotients.Index ({K.kernel.val} : Finset (Setoid M)),
      MulAction G (CanonicalQuotients.Carrier k) := CanonicalQuotients.action S H K.data
  exact RealClosure.Bounds.sortSource_homogeneous (CanonicalQuotients.source S H K.data) K.index
    (CanonicalQuotients.homogeneous S H cco K.data)

theorem exactQuotientSource_cco
    (cco : SemanticCCO.{0,v,v,w} S) (K : FiniteExactKernel S) :
    SemanticCCO.{0,v,v,v} (exactQuotientSource S H K) := by
  letI : ∀ k : CanonicalQuotients.Index ({K.kernel.val} : Finset (Setoid M)),
      MulAction G (CanonicalQuotients.Carrier k) := CanonicalQuotients.action S H K.data
  exact RealClosure.Bounds.sortSource_semanticCCO (CanonicalQuotients.source S H K.data) K.index
    (CanonicalQuotients.semanticCCO S H cco K.data)

theorem exactQuotient_countable [Countable M] (K : FiniteExactKernel S) :
    Countable (Quotient K.kernel.val) :=
  (Quotient.mk''_surjective : Function.Surjective
    (Quotient.mk'' : M → Quotient K.kernel.val)).countable

theorem exactQuotient_projection_not_injective (K : FiniteExactKernel S) :
    ¬Function.Injective (Quotient.mk'' : M → Quotient K.kernel.val) := by
  intro h
  apply K.proper
  apply ColourEq.ext
  intro x y
  change K.kernel x y ↔ x = y
  exact ⟨fun hxy => h (Quotient.sound hxy), fun hxy => hxy ▸ K.kernel.val.refl x⟩

theorem exactQuotient_palette_lt [Countable M]
    (cco : SemanticCCO.{0,v,v,w} S) (K : FiniteExactKernel S) :
    Nat.card ((exactQuotientSource S H K).Atom () ()) < Nat.card (S.Atom () ()) := by
  letI := exactQuotientAction S H K
  have hH := exactQuotientSource_homogeneous S H cco K
  have equivπ : ∀ (g : G) (x : M),
      (Quotient.mk'' : M → Quotient K.kernel.val) (g • x) =
        g • (Quotient.mk'' : M → Quotient K.kernel.val) x := by
    intro g x
    rfl
  have invariantT : ∀ (g : G) (x y : Quotient K.kernel.val),
      (exactQuotientSource S H K).colour (i := ()) (j := ()) (g • x) (g • y) =
        (exactQuotientSource S H K).colour (i := ()) (j := ()) x y :=
    fun g x y => (exactQuotientSource S H K).colourInvariant_of_homogeneous hH g x y
  letI := S.finiteAtom () ()
  letI := (exactQuotientSource S H K).finiteAtom () ()
  simpa only [Nat.card_eq_fintype_card] using
    quotient_diversity_palette_lt S (exactQuotientSource S H K) H
      (Quotient.mk'' : M → Quotient K.kernel.val) Quotient.mk''_surjective
      equivπ invariantT (exactQuotient_projection_not_injective S K)

/-- Fixed-universe tail nodes retain the SAME ambient group, actual source
homogeneity and semantic CCO, and countability through each genuine quotient. -/
structure SourceNode (G : Type t) [Group G] where
  Carrier : Type v
  source : AtomicSource.{0,v,v} Unit (fun _ => Carrier)
  action : MulAction G Carrier
  countable : Countable Carrier
  homogeneous : letI := action; HomogeneousSource source G
  cycles : SemanticCCO.{0,v,v,v} source

instance (N : SourceNode.{v,t} G) : MulAction G N.Carrier := N.action
instance (N : SourceNode.{v,t} G) : Countable N.Carrier := N.countable

noncomputable def quotientNode [Countable M]
    (cco : SemanticCCO.{0,v,v,w} S) (K : FiniteExactKernel S) : SourceNode.{v,t} G where
  Carrier := Quotient K.kernel.val
  source := exactQuotientSource S H K
  action := exactQuotientAction S H K
  countable := exactQuotient_countable S K
  homogeneous := exactQuotientSource_homogeneous S H cco K
  cycles := exactQuotientSource_cco S H cco K

end CCO.FinitePackets.Normalization
