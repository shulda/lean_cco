import CCO.UnaryHN.TypedTransfer
import CCO.UnaryHN.TypedEdge
import CCO.UnaryHN.RawEncoding.OrderedReadout
import CCO.UnaryHN.OrderCycles

/-! The five B037 source exports, in the actual typed presentation. The
Ramsey output colours ALL full induced ordered embeddings. Uniform local
finiteness is proved in the LARGER unrestricted one-sorted ambient. -/

universe u v w
namespace CCO.UnaryHN.Source

open CCO.UnarySupport (Signature)

def OrderedRamsey {L : Signature.{u}} (K : Raw.Class.{u,v} L) : Prop :=
  ∀ {V W : Type v} [Finite V] [Finite W] [LinearOrder V] [LinearOrder W]
    (A : Raw.Typed L V) (B : Raw.Typed L W), K A → K B →
    ∀ (κ : Type w) [Fintype κ] [Nonempty κ],
      ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X) (C : Raw.Typed L X),
        K C ∧ @Raw.OrderedArrow L V W X A B C inferInstance inferInstance o κ

abbrev UniformLocalFiniteness {L : Signature.{u}} (K : Raw.Class.{u,v} L) (N : ℤ) :=
  Native.UniformlyLocallyFinite (Native.OrderedClass (Raw.EncodedClass K))
    (Native.AllOrderedModels (Raw.language L)) (Native.obstructionCutoff N)

theorem orderedRamsey_of_native {L : Signature.{u}} {K : Raw.Class.{u,v} L}
    (h : Native.Ramsey.{u,v,w} (Native.OrderedClass (Raw.EncodedClass K))) :
    OrderedRamsey.{u,v,w} K := by
  intro V W hV hW oV oW A B hA hB κ hκ hκn
  have hEA : Native.OrderedClass (Raw.EncodedClass K) (Raw.encode A).withLinearOrder :=
    ⟨Raw.encode A, oV, ⟨A, hA, rfl⟩, rfl⟩
  have hEB : Native.OrderedClass (Raw.EncodedClass K) (Raw.encode B).withLinearOrder :=
    ⟨Raw.encode B, oW, ⟨B, hB, rfl⟩, rfl⟩
  obtain ⟨X, hX, C, ⟨old, o, ⟨T, hT, rfl⟩, rfl⟩, hArrow⟩ :=
    h (Raw.encode A).withLinearOrder (Raw.encode B).withLinearOrder hEA hEB κ
  let : LinearOrder X := o
  exact ⟨X, hX, o, T, hT, (Raw.orderedArrow_encode_iff A B T κ).mp hArrow⟩

/-- `lem:typed-unary-binary-irreducibility`: retain total source functions. -/
theorem typed_unary_binary_irreducibility {L : Signature.{u}} {V : Type v}
    (C : Raw.Typed L V) (hTotal : C.Total) (hCover : Raw.PairCoverage C) : C.Irreducible :=
  Raw.typed_unary_binary_irreducibility C hTotal hCover

/-- `lem:typed-universal-edge-hn-reflection`: the SAME given f, independently
of every obstruction bound and every SAP assumption. -/
theorem typed_universal_edge_reflection {L : Signature.{u}} {K : Raw.Class.{u,v} L}
    (hRigid : Raw.CompletedMapRigidity K) {V W : Type v}
    (C : StructuralRamsey.Structure (Native.edgeLanguage (Raw.language L)) V)
    (hPieces : Native.IrreduciblesIn (Native.ExpandedClass (Raw.EncodedClass K)) C)
    (H : Raw.Typed L W) (hH : K H) (f : V → W)
    (hf : Native.HE (Native.edgeReduct C) (Raw.encode H) f) :
    Native.HE C (Native.expandEdge (Raw.encode H)) f :=
  Raw.same_map_universal_edge hRigid C hPieces H hH f hf

/-- `thm:unary-hn-irreducible-source-transfer`: every provider is discharged. -/
theorem unary_hn_irreducible_source_transfer {L : Signature.{u}} {K : Raw.Class.{u,v} L}
    {N : ℤ} (hK : Raw.FiniteHereditarySAP K) (hCompleted : Raw.CompletedClass K)
    (hIrr : Raw.AllIrreducible K) (hN : Raw.RestrictedObstruction K N) :
    UniformLocalFiniteness K N ∧ OrderedRamsey.{u,v,w} K := by
  have h := Raw.typed_restricted_transfer hK hCompleted hIrr hN
  exact ⟨h.1, orderedRamsey_of_native h.2⟩

/-- `thm:typed-direct-irreducible-unary-HN`: the main restricted premise is
PROVED from actual completed singleton diagrams by the selected B034 result. -/
theorem typed_direct_irreducible_unary_hn {L : Signature.{u}} {K : Raw.Class.{u,v} L}
    {N : ℤ} (hK : Raw.FiniteHereditarySAP K) (hCompleted : Raw.CompletedClass K)
    (hIrr : Raw.AllIrreducible K) (hN : Raw.DirectObstruction K N) :
    UniformLocalFiniteness K N ∧ OrderedRamsey.{u,v,w} K := by
  have h := Raw.typed_direct_transfer hK hCompleted hIrr hN
  exact ⟨h.1, orderedRamsey_of_native h.2⟩

/-- `thm:typed-abstract-unary-HN-ramsey`: binary coverage DISCHARGES class
irreducibility; the supplied direct N-bound remains an explicit premise. -/
theorem typed_abstract_unary_hn_ramsey {L : Signature.{u}} {K : Raw.Class.{u,v} L}
    {N : ℤ} (hK : Raw.FiniteHereditarySAP K) (hCompleted : Raw.CompletedClass K)
    (hArity : ∀ R : L.Rel, L.arity R ≤ 2) (hBinary : Raw.BinaryCoverage K)
    (hN : Raw.DirectObstruction K N) :
    UniformLocalFiniteness K N ∧ OrderedRamsey.{u,v,w} K := by
  have h := Raw.typed_binary_transfer hK hCompleted hArity hBinary hN
  exact ⟨h.1, orderedRamsey_of_native h.2⟩

end CCO.UnaryHN.Source
