import CCO.APRamseyReadout.Templates
import Mathlib.Order.Preorder.Finite

/-! C30: a finite globally ordered template has no nontrivial full-code
self-embedding. The actual onSupport extension preserves the named strict
order, so finite-chain rigidity fixes every hidden value and then every
marked root. No Ramsey or expansion-property premise is used. -/

universe u v w z a p
namespace CCO.APRamseyReadout
open CCO.FullCode
noncomputable section

/-- Rigidity is inherited from the ACTUAL global order of the generated
hidden support, through all induced full-code self-maps. -/
theorem finite_ordered_full_code_rigid
    (L : CCO.UnarySupport.Signature.{u}) (hbin : ∀ R, L.arity R = 2)
    {V : Type v} (C : CCO.UnarySupport.Structure L V) [LinearOrder V]
    {A : Type a} [Finite A]
    (N : NormalForms (CCO.TerminalHiddenHN.orderedLanguage L hbin))
    (S : RootScheme (CCO.TerminalHiddenHN.orderedLanguage L hbin))
    (O : Object (CCO.TerminalHiddenHN.orderedStructure L hbin C) S A)
    (hN : N.Valid (CCO.TerminalHiddenHN.orderedStructure L hbin C))
    (f : Structure.Embedding (O.codeStructure N) (O.codeStructure N)) :
    f = Structure.Embedding.id (O.codeStructure N) := by
  letI : Finite O.support := (O.support_finite N hN).to_subtype
  let full := Object.embeddingOfCode f
  let g := full.onSupport hN hN
  have hmono : StrictMono g.point := by
    intro x y hxy
    have h := (g.binary_iff (.inr (C.sort x.val,C.sort y.val)) x y).mpr
      ⟨rfl,rfl,hxy⟩
    exact h.2.2
  have hfixed : ∀ x, g.point x = x := fun _ => hmono.apply_eq
  apply Structure.Embedding.ext
  intro x
  apply O.injective
  symm
  refine Root.ext_coordinates (full.tag_eq x).symm ?_
  intro j
  have h := congrArg Subtype.val
    (hfixed ⟨(O.root x).coordinate j,O.coordinate_mem_support x j⟩)
  change full.extendPoint hN ⟨(O.root x).coordinate j,O.coordinate_mem_support x j⟩ =
    (O.root x).coordinate j at h
  exact h.symm.trans (full.extendPoint_coordinate hN hN x j)

variable (B : CCO.CloneTupleGeometry.OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (F : Charts.{u,v,w,p} B)

/-- Concrete source C30. Every actual finite hidden host and every
global order on it give rigid fixed-chart marked full-code objects. -/
theorem actual_visible_rigid {V : Type z} {A : Type a} [Finite A]
    (C : CCO.UnarySupport.Structure (Sig B ht) V) [LinearOrder V]
    (hC : ActualAge B ht C)
    (O : Object (OrderedCoordinateModel B ht C) (orderedTupleScheme B ht F) A)
    (f : Structure.Embedding (O.codeStructure (orderedTupleNormalForms B ht))
      (O.codeStructure (orderedTupleNormalForms B ht))) :
    f = Structure.Embedding.id (O.codeStructure (orderedTupleNormalForms B ht)) :=
  finite_ordered_full_code_rigid (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) C
    (orderedTupleNormalForms B ht) (orderedTupleScheme B ht F) O
    (orderedTupleNormalForms_valid_of_actualAge B ht C hC) f

/-- Membership in the actual ALL-orders age provides the global order
and normal-form discharge internally, on the SAME entire hidden host. -/
theorem actual_ordered_visible_rigid {A : Type a} [Finite A]
    (D : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht))
    (hD : OrderedAge B ht D)
    (O : Object D.model (orderedTupleScheme B ht F) A)
    (f : Structure.Embedding (O.codeStructure (orderedTupleNormalForms B ht))
      (O.codeStructure (orderedTupleNormalForms B ht))) :
    f = Structure.Embedding.id (O.codeStructure (orderedTupleNormalForms B ht)) := by
  obtain ⟨C,o,hC,he⟩ := hD
  cases D with | mk V M hV =>
    dsimp only at C o hC he O f ⊢
    subst M
    letI : LinearOrder V := o
    exact actual_visible_rigid B ht F C hC O f

end
end CCO.APRamseyReadout
