import CCO.APRamseyReadout.OrderedRigidity
import CCO.APRamseyReadout.RamseyReadout

/-! The concrete C30 source consumer for the ACTUAL finite relational
readout expansions. Their selected old self-maps induce the exact ordered
full-code self-maps already proved rigid. The smaller-language equivalence
keeps the very same old map. No second finite-order argument is used. -/

universe u v w p
namespace CCO.APRamseyReadout
open CCO.FullCode CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
local notation "Γ" => actualTupleInterpretation B ht F

/-- Every actual full relational readout self-embedding fixes each
original vertex, by rigidity of its SAME selected ordered template. -/
theorem actual_full_readout_rigid {A : CCO.FiniteInduced (X := B.Point)}
    (a : (actualFullReadoutData B ht F).Expansion A)
    (f : (actualFullReadoutData B ht F).Embedding a a) (x : A.vertices) :
    f.old.toEmbedding x = x := by
  letI : Finite A.vertices := A.finite_vertices.to_subtype
  letI : LinearOrder (actualTupleSupport B ht F A) := a.order
  let rf := (Γ).relationalToReadout B.homogeneous f
  let hf := actualTemplateEmbedding B ht F rf
  let N := orderedTupleNormalForms B ht
  let O := actualOrderedObject B ht F a
  have roots (y : A.vertices) : (O.root y).map hf = O.root (rf.old.toEmbedding y) :=
    actualTemplateEmbedding_root B ht F rf y
  let code : Object.Embedding N O O := {
    point := rf.old.toEmbedding
    injective := rf.old.toEmbedding.injective
    tag_eq := fun y => (congrArg Root.tag (roots y)).symm
    equality_iff := by
      intro y z p q
      rw [← roots y,← roots z]
      exact equalityCode_map N hf _ _ p q
    unary_iff := by
      intro U y p
      rw [← roots y]
      exact unaryCode_map N hf U _ p
    binary_iff := by
      intro R y z p q
      rw [← roots y,← roots z]
      exact binaryCode_map N hf R _ _ p q }
  have hid := actual_visible_rigid B ht F (actualTemplateRaw B ht F A)
    (actualTemplateRaw_mem B ht F A) O code.asCodeEmbedding
  exact congrArg (fun g => g.point x) hid

/-- Deleting the proved definable predicates and cross-sort comparisons
changes no embedding map; rigidity therefore holds in the actual smaller
finite language on each prescribed block expansion as well. -/
theorem actual_small_readout_rigid
    (priority : LinearOrder (CoordinateLanguage B ht).Sorts)
    {A : CCO.FiniteInduced (X := B.Point)}
    (a : (actualSmallReadoutData B ht F priority).Expansion A)
    (f : (actualSmallReadoutData B ht F priority).Embedding a a) (x : A.vertices) :
    f.old.toEmbedding x = x :=
  actual_full_readout_rigid B ht F a.val
    (((Γ).fullSmallReadoutEmbeddingEquiv priority B.homogeneous a a).symm f) x

end
end CCO.APRamseyReadout
