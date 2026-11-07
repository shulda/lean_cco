import CCO.TerminalHiddenHN.OrderedCodec
import CCO.TerminalHiddenHN.ActualAge
import CCO.TerminalHiddenHN.NormalForms
import CCO.FullCode.FiniteHidden

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
