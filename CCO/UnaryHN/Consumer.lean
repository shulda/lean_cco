import CCO.UnaryHN.Source

/-! Actual consumers of the five source exports. Witnesses have genuine
typed K diagrams on their ENTIRE finite carrier, and every colour is on
actual induced ordered embeddings. The local consumer retains only global
injection and HE; it never asserts global inducedness of a reducible source. -/

universe u v w
namespace CCO.UnaryHN

open CCO.UnarySupport (Signature)

theorem constructed_ordered_ramsey_use {L : Signature.{u}} {K : Raw.Class.{u,v} L}
    {N : ℤ} (hK : Raw.FiniteHereditarySAP K) (hCompleted : Raw.CompletedClass K)
    (hIrr : Raw.AllIrreducible K) (hN : Raw.DirectObstruction K N)
    {V W : Type v} [Finite V] [Finite W] [LinearOrder V] [LinearOrder W]
    (A : Raw.Typed L V) (B : Raw.Typed L W) (hA : K A) (hB : K B)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X) (C : Raw.Typed L X),
      K C ∧ C.Total ∧
        @Raw.OrderedArrow L V W X A B C inferInstance inferInstance o κ := by
  have hRamsey : Source.OrderedRamsey.{u,v,w} K :=
    (Source.typed_direct_irreducible_unary_hn hK hCompleted hIrr hN).2
  obtain ⟨X, hX, o, C, hC, hArrow⟩ := hRamsey (V := V) (W := W) A B hA hB κ
  let : Finite X := hX
  exact ⟨X, hX, o, C, hC, hCompleted C hC, hArrow⟩

theorem constructed_strong_local_use {L : Signature.{u}} {K : Raw.Class.{u,v} L}
    {N : ℤ} (hK : Raw.FiniteHereditarySAP K) (hCompleted : Raw.CompletedClass K)
    (hIrr : Raw.AllIrreducible K) (hN : Raw.RestrictedObstruction K N)
    {P V : Type v} [Finite P] [Finite V]
    (C₀ : StructuralRamsey.Structure (Raw.language L).withLinearOrder P)
    (hC₀ : Native.AllOrderedModels (Raw.language L) C₀)
    (C : StructuralRamsey.Structure (Raw.language L).withLinearOrder V)
    (hSingle : C.SingletonValued) (p : V → P) (hp : Native.HE C C₀ p)
    (hPieces : Native.IrreduciblesIn (Native.OrderedClass (Raw.EncodedClass K)) C)
    (hTests : Native.ClosedSmallCompletable (Native.OrderedClass (Raw.EncodedClass K))
      C (Native.obstructionCutoff N)) :
    ∃ (X : Type v) (_ : Finite X) (o : LinearOrder X) (T : Raw.Typed L X),
      K T ∧ T.Total ∧ ∃ q : V → X,
        Native.HE C (@StructuralRamsey.Structure.withLinearOrder (Raw.language L) X
          (Raw.encode T) o.toLT) q ∧ Function.Injective q := by
  have h := Native.strong_ordered_completion_at_cutoff (Raw.unary_language L)
    (Raw.encoded_finiteHereditarySAP hK) (Raw.encoded_allIrreducible hIrr)
    (Raw.encoded_restrictedObstruction hCompleted hN) C₀ hC₀ C hSingle p hp hPieces hTests
  obtain ⟨X, hX, Target, ⟨old, o, ⟨T, hT, rfl⟩, rfl⟩, q, hq, hInjective⟩ := h
  let : Finite X := hX
  exact ⟨X, hX, o, T, hT, hCompleted T hT, q, hq, hInjective⟩

end CCO.UnaryHN
