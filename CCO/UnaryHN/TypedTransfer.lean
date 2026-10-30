import CCO.UnaryHN.NativeTransfer
import CCO.UnaryHN.RawEncoding.Obstruction

/-! Actual typed instances of the fully discharged native transfer. Raw
local candidates are decoded from their actual irreducibles BEFORE the
typed obstruction is applied. Only the supplied restricted/direct integer
bound remains; the direct and binary hypotheses are genuinely discharged. -/

universe u v w
namespace CCO.UnaryHN.Raw

open CCO.UnarySupport (Signature)

theorem typed_restricted_transfer {L : Signature.{u}} {K : Class.{u,v} L} {N : ℤ}
    (hK : FiniteHereditarySAP K) (hCompleted : CompletedClass K)
    (hIrr : AllIrreducible K) (hN : RestrictedObstruction K N) :
    Native.UniformlyLocallyFinite (Native.OrderedClass (EncodedClass K))
      (Native.AllOrderedModels (language L)) (Native.obstructionCutoff N) ∧
      Native.Ramsey.{u,v,w} (Native.OrderedClass (EncodedClass K)) :=
  Native.unary_ordered_transfer (unary_language L) (encoded_finiteHereditarySAP hK)
    (encoded_allIrreducible hIrr) (encoded_restrictedObstruction hCompleted hN)

theorem typed_direct_transfer {L : Signature.{u}} {K : Class.{u,v} L} {N : ℤ}
    (hK : FiniteHereditarySAP K) (hCompleted : CompletedClass K)
    (hIrr : AllIrreducible K) (hN : DirectObstruction K N) :
    Native.UniformlyLocallyFinite (Native.OrderedClass (EncodedClass K))
      (Native.AllOrderedModels (language L)) (Native.obstructionCutoff N) ∧
      Native.Ramsey.{u,v,w} (Native.OrderedClass (EncodedClass K)) :=
  typed_restricted_transfer hK hCompleted hIrr (restricted_of_direct hCompleted hN)

theorem typed_binary_transfer {L : Signature.{u}} {K : Class.{u,v} L} {N : ℤ}
    (hK : FiniteHereditarySAP K) (hCompleted : CompletedClass K)
    (hArity : ∀ R : L.Rel, L.arity R ≤ 2)
    (hBinary : ∀ {V : Type v} (C : Typed L V), K C →
      ∀ x y, x ≠ y → BinaryEdge C x y) (hN : DirectObstruction K N) :
    Native.UniformlyLocallyFinite (Native.OrderedClass (EncodedClass K))
      (Native.AllOrderedModels (language L)) (Native.obstructionCutoff N) ∧
      Native.Ramsey.{u,v,w} (Native.OrderedClass (EncodedClass K)) :=
  typed_direct_transfer hK hCompleted (allIrreducible_of_binary hK hCompleted hArity hBinary) hN

end CCO.UnaryHN.Raw
