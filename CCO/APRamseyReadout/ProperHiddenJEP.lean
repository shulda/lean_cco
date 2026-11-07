import CCO.APRamseyReadout.ProperHiddenAge
import CCO.TerminalHiddenHN.FiniteOrderExtension
import Mathlib.Data.Sum.Order

/-! Joint embedding for the entire ALL-global-orders hidden age.
Strong amalgamation over the empty base makes the two supplied images
disjoint. Their prescribed orders concatenate and extend to the actual
finite amalgam, so both original ordered maps are retained literally. -/

universe u v w z
namespace CCO.APRamseyReadout
open CCO.TerminalHiddenHN CCO.CloneTupleGeometry
noncomputable section

/-- Whole unordered SAP supplies ordered JEP for ALL orders on every
member. No compatibility condition on the two prescribed orders occurs. -/
theorem orderedFullCodeAge_jep_of_sap
    (L : CCO.UnarySupport.Signature.{u}) (hbin : ∀ R, L.arity R = 2)
    {K : CCO.UnaryHN.Raw.Class.{u,z} L}
    (hK : CCO.UnaryHN.Raw.FiniteHereditarySAP K)
    (A E : CCO.FullCode.FiniteHidden.{u,z} (orderedLanguage L hbin))
    (hA : orderedFullCodeAge L hbin K A) (hE : orderedFullCodeAge L hbin K E) :
    ∃ D : CCO.FullCode.FiniteHidden.{u,z} (orderedLanguage L hbin),
      orderedFullCodeAge L hbin K D ∧
      Nonempty (CCO.FullCode.Structure.Embedding A.model D.model) ∧
      Nonempty (CCO.FullCode.Structure.Embedding E.model D.model) := by
  classical
  rcases A with ⟨V,M,hV⟩
  rcases E with ⟨W,N,hW⟩
  obtain ⟨C,oC,hC,hM⟩ := hA
  obtain ⟨F,oF,hF,hN⟩ := hE
  dsimp only at C oC hC hM F oF hF hN ⊢
  subst M
  subst N
  letI : LinearOrder V := oC
  letI : LinearOrder W := oF
  let Root := C.induce ∅ C.isClosed_empty
  let s : Root.Embedding C := C.inclusion ∅ C.isClosed_empty
  let t : Root.Embedding F := {
    point := fun x => False.elim x.property
    sort_eq := fun x => False.elim x.property
    map_func := fun _ x _ _ => False.elim x.property
    map_rel := by
      intro R xs _
      exact False.elim (xs ⟨0,by rw [hbin R]; decide⟩).property
    injective := fun x _ _ => False.elim x.property
    reflect_func := fun _ x _ _ => False.elim x.property
    reflect_rel := by
      intro R xs _
      exact False.elim (xs ⟨0,by rw [hbin R]; decide⟩).property }
  obtain ⟨Q,hQ,D,hD,l,r,_,hInt⟩ := hK.strong hC hF s t
  letI : Finite Q := hQ
  let joined : V ⊕ₗ W → Q := fun x => Sum.elim l.point r.point (ofLex x)
  have raw_injective : Function.Injective (Sum.elim l.point r.point : V ⊕ W → Q) := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact congrArg Sum.inl (l.injective hxy)
      | inr y =>
        obtain ⟨a,_,_⟩ := hInt x y hxy
        exact False.elim a.property
    | inr x =>
      cases y with
      | inl y =>
        obtain ⟨a,_,_⟩ := hInt y x hxy.symm
        exact False.elim a.property
      | inr y =>
        exact congrArg Sum.inr (r.injective hxy)
  have joined_injective : Function.Injective joined := by
    intro x y hxy
    exact congrArg (fun a : V ⊕ W => (toLex a : V ⊕ₗ W)) (raw_injective hxy)
  obtain ⟨oD,hOrder⟩ := finite_linearOrder_extension joined joined_injective
  letI : LinearOrder Q := oD
  let lOrdered : CCO.UnaryHN.Raw.OrderedEmbedding C D := {
    toEmbedding := l
    order_iff := by
      intro x y
      exact (hOrder (toLex (Sum.inl x)) (toLex (Sum.inl y))).trans
        Sum.Lex.inl_lt_inl_iff }
  let rOrdered : CCO.UnaryHN.Raw.OrderedEmbedding F D := {
    toEmbedding := r
    order_iff := by
      intro x y
      exact (hOrder (toLex (Sum.inr x)) (toLex (Sum.inr y))).trans
        Sum.Lex.inr_lt_inr_iff }
  refine ⟨⟨Q,orderedStructure L hbin D,hQ⟩,?_,?_,?_⟩
  · exact ⟨D,oD,hD,rfl⟩
  · exact ⟨orderedEmbedding L hbin lOrdered⟩
  · exact ⟨orderedEmbedding L hbin rOrdered⟩

/-- The SAME actual B059 whole hidden age has JEP with ALL prescribed
global orders and arbitrary finite carrier presentations, orphans included. -/
theorem whole_ordered_jep (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
    (A E : CCO.FullCode.FiniteHidden.{max u v w,z}
      (orderedLanguage (Sig B ht)
        (sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht))))
    (hA : OrderedAge B ht A) (hE : OrderedAge B ht E) :
    ∃ D : CCO.FullCode.FiniteHidden.{max u v w,z}
      (orderedLanguage (Sig B ht)
        (sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht))),
      OrderedAge B ht D ∧
      Nonempty (CCO.FullCode.Structure.Embedding A.model D.model) ∧
      Nonempty (CCO.FullCode.Structure.Embedding E.model D.model) :=
  orderedFullCodeAge_jep_of_sap (Sig B ht)
    (sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht))
    (whole_age_sap B ht) A E hA hE

/-- Apply the proved unary-closed sort restriction to the SAME whole
ordered age. All proper sorts, including orphan-only members, remain. -/
theorem proper_ordered_jep (B : OwnerStage.{u,v,w}) (ht : B.Terminal) :
    FullJointEmbedding
      (orderedLanguage (Sig B ht)
        (sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)))
      (ProperOrderedAge.{u,v,w,z} B ht) := by
  let L := TerminalHiddenHN.orderedLanguage (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht))
  let I : Set L.Sorts := fun s => ProperSort B ht s
  have hI : ∀ F : L.Func, L.input F ∈ I → L.output F ∈ I := by
    intro F _
    exact properSort_output B ht F
  have hK : FullHereditary L (OrderedAge.{u,v,w,z} B ht) := by
    intro A D hD e
    exact whole_ordered_of_embedding B ht hD e
  exact fullCode_sort_restriction_jep L I hI hK (whole_ordered_jep B ht)

end
end CCO.APRamseyReadout
