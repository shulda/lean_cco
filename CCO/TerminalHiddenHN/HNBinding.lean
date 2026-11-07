import CCO.TerminalHiddenHN.ActualSAP
import CCO.TerminalHiddenHN.Irreducibility
import CCO.TerminalHiddenHN.ObstructionBinding
import CCO.UnaryHN.Consumer

/-! Source17/18 C35--C36: the existing direct unary HN theorem is
instantiated on the ENTIRE actual hidden age. Its finite hereditary SAP,
completed-member irreducibility and exact admitted obstruction gate are
all proved source instances. Arbitrary global hidden orders and every
full induced ordered embedding remain in the conclusion.

No Ramsey, completion, obstruction or external-theorem provider is an
additional premise. The three accepted HN bindings are reused unchanged;
the received source16 forest theorem remains inside the geometric bound.
-/

universe u v w r z t
namespace CCO.TerminalHiddenHN
open CCO.UnarySupport CCO.UnarySupport.Structure CCO.UnaryHN
open CCO.TypedOrbitFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))
variable [∀ i, Countable (X i)]
variable (cco : SemanticCCO.{u,v,max u v,w} S)

include cco

/-- The SAME geometric cutoff works in the larger unrestricted ordered
HN ambient; the entire actual hidden age with ALL global orders is Ramsey. -/
theorem actual_hidden_hn :
    Source.UniformLocalFiniteness (ActualAge.{u,v,w,r,z} S H sap hCover) (obstructionBound S H) ∧
      Source.OrderedRamsey.{max u v w,z,t} (ActualAge S H sap hCover) :=
  Source.typed_direct_irreducible_unary_hn
    (actualAge_finiteHereditarySAP S H sap hCover cco)
    (actualAge_completed S H sap hCover)
    (actualAge_allIrreducible S H sap hCover)
    (actual_directObstruction S H sap hCover cco)

/-- Standalone C35 source export, before real-root readout. -/
theorem actual_hidden_uniform_local_finiteness :
    Source.UniformLocalFiniteness (ActualAge.{u,v,w,r,z} S H sap hCover) (obstructionBound S H) :=
  (actual_hidden_hn.{u,v,w,r,z,0} S H sap hCover cco).1

/-- Standalone C36 source export consumed by the ordered hidden codec
and later B061. There is no point-generation or no-orphan restriction. -/
theorem actual_hidden_ordered_ramsey :
    Source.OrderedRamsey.{max u v w,z,t} (ActualAge.{u,v,w,r,z} S H sap hCover) :=
  (actual_hidden_hn S H sap hCover cco).2

/-- The exact HN local test produces a globally injective HE into an
actual finite ordered completed member, extending the displayed source
order. The projection remains into an arbitrary ordered ambient C₀. -/
theorem actual_hidden_strong_local_completion
    {P V : Type z} [Finite P] [Finite V]
    (C₀ : StructuralRamsey.Structure (Raw.language (Sig S H sap hCover)).withLinearOrder P)
    (hC₀ : Native.AllOrderedModels (Raw.language (Sig S H sap hCover)) C₀)
    (C : StructuralRamsey.Structure (Raw.language (Sig S H sap hCover)).withLinearOrder V)
    (hSingle : C.SingletonValued) (p : V → P) (hp : Native.HE C C₀ p)
    (hPieces : Native.IrreduciblesIn
      (Native.OrderedClass (Raw.EncodedClass (ActualAge S H sap hCover))) C)
    (hTests : Native.ClosedSmallCompletable
      (Native.OrderedClass (Raw.EncodedClass (ActualAge S H sap hCover)))
      C (obstructionCutoff S H)) :
    ∃ (W : Type z) (_ : Finite W) (o : LinearOrder W) (T : Raw.Typed (Sig S H sap hCover) W),
      ActualAge S H sap hCover T ∧ T.Total ∧ ∃ q : V → W,
        Native.HE C (@StructuralRamsey.Structure.withLinearOrder (Raw.language (Sig S H sap hCover)) W
          (Raw.encode T) o.toLT) q ∧ Function.Injective q :=
  CCO.UnaryHN.constructed_strong_local_use
    (actualAge_finiteHereditarySAP S H sap hCover cco)
    (actualAge_completed S H sap hCover)
    (actualAge_allIrreducible S H sap hCover)
    (Raw.restricted_of_direct (actualAge_completed S H sap hCover)
      (actual_directObstruction S H sap hCover cco)) C₀ hC₀ C hSingle p hp hPieces hTests

end
end CCO.TerminalHiddenHN
