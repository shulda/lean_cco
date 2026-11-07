import CCO.TerminalHiddenHN.OrderedCodec
import CCO.TerminalHiddenHN.ActualAge
import CCO.TerminalHiddenHN.NormalForms
import CCO.FullCode.FiniteHidden
import Mathlib.Order.Basic

/-! The ENTIRE ordered hidden age. The order is arbitrary on the whole
finite carrier, including every orphan; no root-generated restriction is
imposed. Literal induced closed subobjects retain the same order. -/

universe u v w r z
namespace CCO.TerminalHiddenHN
noncomputable section
variable (L : CCO.UnarySupport.Signature.{u}) (hbin : ∀ R, L.arity R = 2)

theorem orderedStructure_induce {V : Type v} (C : CCO.UnarySupport.Structure L V)
    [LinearOrder V] (T : Set V) (hT : C.IsClosed T) :
    orderedStructure L hbin (C.induce T hT) =
      (orderedStructure L hbin C).induce T hT := by
  refine fullStructure_ext
    (C := orderedStructure L hbin (C.induce T hT))
    (D := (orderedStructure L hbin C).induce T hT) rfl rfl ?_ ?_
  · funext U
    exact PEmpty.elim U
  · funext R x y
    cases R with
    | inl R =>
      change C.rel R (Subtype.val ∘ binaryTuple L R x y) =
        C.rel R (binaryTuple L R x.val y.val)
      exact congrArg (C.rel R) (binaryTuple_map L R Subtype.val x y).symm
    | inr p => rfl

/-- All actual finite class members, with ALL global strict orders and
all their arbitrary carrier presentations. -/
def orderedFullCodeAge (K : CCO.UnaryHN.Raw.Class.{u,v} L)
    (D : CCO.FullCode.FiniteHidden.{u,v} (orderedLanguage L hbin)) : Prop :=
  ∃ (C : CCO.UnarySupport.Structure L D.Carrier) (o : LinearOrder D.Carrier),
    K C ∧ D.model = @orderedStructure L hbin D.Carrier C o

/-- Class membership is invariant under ALL full induced embeddings,
not just the chosen carrier presentation or a root-generated shadow. -/
theorem orderedFullCodeAge_of_embedding {K : CCO.UnaryHN.Raw.Class.{u,v} L}
    (hK : CCO.UnaryHN.Raw.Hereditary K)
    {E D : CCO.FullCode.FiniteHidden.{u,v} (orderedLanguage L hbin)}
    (hD : orderedFullCodeAge L hbin K D)
    (e : CCO.FullCode.Structure.Embedding E.model D.model) :
    orderedFullCodeAge L hbin K E := by
  rcases D with ⟨W,N,hW⟩
  obtain ⟨C,oC,hC,he⟩ := hD
  dsimp only at C oC hC he e ⊢
  subst N
  letI : LinearOrder W := oC
  let U := binaryDecode L hbin (orderedBinaryReduct L hbin E.model)
  let oE : LinearOrder E.Carrier := LinearOrder.lift' e.point e.injective
  letI : LinearOrder E.Carrier := oE
  have hC' : K (binaryDecode L hbin (orderedBinaryReduct L hbin (orderedStructure L hbin C))) := by
    change K (binaryDecode L hbin (binaryStructure L hbin C))
    exact (binaryDecode_binaryStructure L hbin C).symm ▸ hC
  have hU : K U := hK hC' (binaryDecodeEmbedding L hbin (orderedReductEmbedding L hbin e))
  refine ⟨U,oE,hU,?_⟩
  refine fullStructure_ext (C := E.model) (D := orderedStructure L hbin U) rfl rfl ?_ ?_
  · funext R
    exact PEmpty.elim R
  · funext R x y
    cases R with
    | inl R =>
      change E.model.binary (.inl R) x y = E.model.binary (.inl R)
        (binaryTuple L R x y (binaryFirst L hbin R))
        (binaryTuple L R x y (binarySecond L hbin R))
      rw [binaryTuple_first,binaryTuple_second]
    | inr p =>
      apply propext
      have hb := e.binary_iff (.inr p) x y
      have hx : C.sort (e.point x) = E.model.sort x := e.sort_eq x
      have hy : C.sort (e.point y) = E.model.sort y := e.sort_eq y
      change E.model.binary (.inr p) x y ↔
        (E.model.sort x = p.1 ∧ E.model.sort y = p.2 ∧ e.point x < e.point y)
      exact hb.symm.trans (by
        change (C.sort (e.point x) = p.1 ∧ C.sort (e.point y) = p.2 ∧ e.point x < e.point y) ↔ _
        rw [hx,hy])

theorem orderedFullCodeAge_hereditary {K : CCO.UnaryHN.Raw.Class.{u,v} L}
    (hK : CCO.UnaryHN.Raw.Hereditary K) :
    CCO.FullCode.HereditaryHidden (orderedFullCodeAge L hbin K) := by
  intro D hD T hT
  rcases D with ⟨V,M,hV⟩
  obtain ⟨C,o,hC,he⟩ := hD
  dsimp only at C o hC he T hT ⊢
  subst M
  letI : Finite V := hV
  letI : LinearOrder V := o
  refine ⟨C.induce T hT,(inferInstance : LinearOrder T),hK hC (C.inclusion T hT),?_⟩
  exact (orderedStructure_induce L hbin C T hT).symm

section Actual
variable {ι : Type u} {X : ι → Type v} (S : CCO.AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : CCO.HomogeneousSource S G) (sap : CCO.AgeSAP S)
variable (hCover : ∀ i, CCO.TypedOrbitFrames.OriginalAllFullCoversInfinite S (i := i))

abbrev OrderedActualAge :
    CCO.FullCode.FiniteHidden.{max u v w,z}
      (orderedLanguage (Sig S H sap hCover) (sig_binary S H sap hCover)) → Prop :=
  orderedFullCodeAge (Sig S H sap hCover) (sig_binary S H sap hCover)
    (ActualAge.{u,v,w,r,z} S H sap hCover)

theorem orderedActualAge_hereditary :
    CCO.FullCode.HereditaryHidden (OrderedActualAge.{u,v,w,r,z} S H sap hCover) :=
  orderedFullCodeAge_hereditary _ _ (actualAge_hereditary S H sap hCover)

theorem orderedActualAge_of_embedding
    {E D : CCO.FullCode.FiniteHidden.{max u v w,z}
      (orderedLanguage (Sig S H sap hCover) (sig_binary S H sap hCover))}
    (hD : OrderedActualAge S H sap hCover D)
    (e : CCO.FullCode.Structure.Embedding E.model D.model) :
    OrderedActualAge S H sap hCover E :=
  orderedFullCodeAge_of_embedding _ _ (actualAge_hereditary S H sap hCover) hD e

/-- Whole semantic-function normalization is valid at EVERY hidden
origin in EVERY actual member, for ANY choice of its global order. -/
theorem orderedActualAge_normal
    (D : CCO.FullCode.FiniteHidden.{max u v w,z}
      (orderedLanguage (Sig S H sap hCover) (sig_binary S H sap hCover)))
    (hD : OrderedActualAge S H sap hCover D) :
    (orderedNormalForms S H sap hCover).Valid D.model := by
  rcases D with ⟨V,M,hV⟩
  obtain ⟨C,o,hC,he⟩ := hD
  dsimp only at C o hC he ⊢
  subst M
  letI : LinearOrder V := o
  exact orderedNormalForms_valid_of_actualAge S H sap hCover C hC

end Actual
end
end CCO.TerminalHiddenHN
