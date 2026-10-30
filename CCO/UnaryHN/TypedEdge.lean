import CCO.UnaryHN.TypedTransferBasis
import CCO.UnaryHN.UniversalEdge.SameMap

/-! Faithful typed receiving binding of the SAME-map universal-edge result.
The completed old reduct may be reducible; only the stated rigidity on old
HE maps is used. No SAP, obstruction bound or replacement injection is added. -/

universe u v
namespace CCO.UnaryHN.Raw

open CCO.UnarySupport (Signature)

def CompletedMapRigidity {L : Signature.{u}} (K : Class.{u,v} L) : Prop :=
  ∀ {V W : Type v} (C : Typed L V) (D : Typed L W), K C → K D →
    ∀ f : V → W, HE C D f → ∃ e : C.Embedding D, ∀ x, e.point x = f x

theorem encoded_completedMapRigidity {L : Signature.{u}} {K : Class.{u,v} L}
    (h : CompletedMapRigidity K) : Native.CompletedMapRigidity (EncodedClass K) := by
  rintro V W C D ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩ f hf
  obtain ⟨e, he⟩ := h C D hC hD f (HE.of_native hf)
  exact ⟨encodeEmbedding e, he⟩

theorem completedMapRigidity_of_irreducible {L : Signature.{u}} {K : Class.{u,v} L}
    (hK : AllIrreducible K) : CompletedMapRigidity K := by
  intro V W C D hC hD f hf
  obtain ⟨e, he⟩ := Native.completedMapRigidity_of_irreducible
    (encoded_allIrreducible hK) (encode C) (encode D) ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩ f hf.to_native
  exact ⟨decodeEmbedding e, he⟩

theorem completedMapRigidity_of_homomorphisms {L : Signature.{u}} {K : Class.{u,v} L}
    (hK : ∀ {V W : Type v} (C : Typed L V) (D : Typed L W), K C → K D →
      ∀ f : C.Hom D, ∃ e : C.Embedding D, ∀ x, e.point x = f.point x) :
    CompletedMapRigidity K := by
  intro V W C D hC hD f hf
  exact hK C D hC hD ⟨f, hf.sort_eq, hf.map_func, hf.map_rel⟩

theorem same_map_universal_edge {L : Signature.{u}} {K : Class.{u,v} L}
    (hRigid : CompletedMapRigidity K) {V W : Type v}
    (C : StructuralRamsey.Structure (Native.edgeLanguage (language L)) V)
    (hPieces : Native.IrreduciblesIn (Native.ExpandedClass (EncodedClass K)) C)
    (H : Typed L W) (hH : K H) (f : V → W)
    (hf : Native.HE (Native.edgeReduct C) (encode H) f) :
    Native.HE C (Native.expandEdge (encode H)) f :=
  Native.same_map_universal_edge (encoded_completedMapRigidity hRigid) hPieces ⟨H, hH, rfl⟩ hf

end CCO.UnaryHN.Raw
