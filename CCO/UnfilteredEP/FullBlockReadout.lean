import CCO.APRamseyReadout.RamseyReadout
import CCO.APRamseyReadout.VisibleJEP

/-!
# The FULL block-code Ramsey provider before definitional deletion

The variable datum is the whole block order on the canonical generated
support. Every non-order code and every ordered term comparison remains
in the finite language. This provider is constructed independently of EP
and of the automatic core theorem.
-/

universe u v w r l k p
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout
noncomputable section

section Generic
variable {ι : Type u} {X : ι → Type v}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {L : Language.{l}} {V : Type k} {C : Structure L V} {scheme : RootScheme L}
variable {S : AtomicSource.{u,v,w} ι X}
variable (D : TupleInterpretation (G := G) S C scheme)
variable (H : HomogeneousSource S G) (priority : LinearOrder L.Sorts)

/-- C26 uses this FULL finite code provider; no non-order predicate is
deleted before the singleton Ramsey criterion is applied. -/
def fullBlockReadoutExpansion : CCO.TerminalHiddenHN.RealExpansionData.{u,v,w,max u l,k} S where
  Unary := D.FullUnaryName
  Binary := D.FullBinaryName
  finiteUnary := by let := S.finiteSort; infer_instance
  finiteBinary := by let := S.finiteSort; infer_instance
  unarySort q := q.1
  leftSort q := q.1
  rightSort q := q.2.1
  Expansion := D.BlockReadoutOn priority
  nonempty := D.block_readout_nonempty priority
  unary a := D.fullUnary a.val
  binary a := D.fullBinary a.val
  unary_sorted _ _ _ h := h.1
  binary_sorted _ _ _ _ h := ⟨h.1,h.2.1⟩
  faithful a b _hb hc := by
    apply Subtype.ext
    exact D.full_readout_faithful a.val b.val hc
  restrict e b := D.restrictBlockReadout priority H e b
  restrict_unary e b R x :=
    (D.fullReadoutExpansion H).restrict_unary e b.val R x
  restrict_binary e b R x y :=
    (D.fullReadoutExpansion H).restrict_binary e b.val R x y

/-- The finite full relational presentation and semantic block support
maps have exactly the same original point maps. -/
def fullBlockToReadout
    {A B : FiniteInduced (X := X)}
    {a : D.BlockReadoutOn priority A} {b : D.BlockReadoutOn priority B}
    (f : (fullBlockReadoutExpansion D H priority).Embedding a b) :
    D.ReadoutEmbedding H a.val b.val :=
  D.relationalToReadout H ⟨f.old,f.unary_iff,f.binary_iff⟩

def readoutToFullBlock
    {A B : FiniteInduced (X := X)}
    {a : D.BlockReadoutOn priority A} {b : D.BlockReadoutOn priority B}
    (f : D.ReadoutEmbedding H a.val b.val) :
    (fullBlockReadoutExpansion D H priority).Embedding a b := by
  let g := D.readoutToRelational H f
  exact ⟨g.old,g.unary_iff,g.binary_iff⟩

@[simp] theorem readoutToFullBlock_old
    {A B : FiniteInduced (X := X)}
    {a : D.BlockReadoutOn priority A} {b : D.BlockReadoutOn priority B}
    (f : D.ReadoutEmbedding H a.val b.val) :
    (readoutToFullBlock D H priority f).old = f.old := rfl

/-- Exact all-embedding equivalence; the only original map is unchanged. -/
def fullBlockReadoutEmbeddingEquiv
    {A B : FiniteInduced (X := X)}
    (a : D.BlockReadoutOn priority A) (b : D.BlockReadoutOn priority B) :
    (fullBlockReadoutExpansion D H priority).Embedding a b ≃
      D.ReadoutEmbedding H a.val b.val where
  toFun := fullBlockToReadout D H priority
  invFun := readoutToFullBlock D H priority
  left_inv _ := CCO.TerminalHiddenHN.RealExpansionData.Embedding.ext (fun _ => rfl)
  right_inv _ := TupleInterpretation.ReadoutEmbedding.ext H (fun _ => rfl)

theorem fullBlockReadoutExpansion_reasonable :
    (fullBlockReadoutExpansion D H priority).Reasonable := by
  intro A B e a
  exact D.block_readout_reasonable priority H e a

/-- The FULL language Ramsey arrows use the actual semantic block arrows;
no predicate deletion theorem or expansion property is used. -/
theorem fullBlockReadoutExpansion_ramsey
    (ramsey : D.BlockReadoutRamsey priority H) :
    (fullBlockReadoutExpansion D H priority).Ramsey := by
  intro A B a b n positive
  obtain ⟨E,c,arrow⟩ := ramsey A B a b n positive
  refine ⟨E,c,?_⟩
  intro colour
  obtain ⟨g,shade,mono⟩ := arrow (fun f => colour (readoutToFullBlock D H priority f))
  refine ⟨readoutToFullBlock D H priority g,?_⟩
  have const (f : (fullBlockReadoutExpansion D H priority).Embedding a b) :
      colour ((readoutToFullBlock D H priority g).comp f) = shade := by
    have he : (readoutToFullBlock D H priority g).comp f =
      readoutToFullBlock D H priority (g.comp H (fullBlockToReadout D H priority f)) :=
      CCO.TerminalHiddenHN.RealExpansionData.Embedding.ext (fun _ => rfl)
    exact (congrArg colour he).trans (mono (fullBlockToReadout D H priority f))
  exact fun f h => (const f).trans (const h).symm

end Generic

open CCO.CloneTupleGeometry
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
variable (priority : LinearOrder (CoordinateLanguage B ht).Sorts)
local notation "Γ" => actualTupleInterpretation B ht F

abbrev actualFullBlockReadoutData := fullBlockReadoutExpansion (Γ) B.homogeneous priority

theorem actual_full_block_readout_ramsey :
    (actualFullBlockReadoutData B ht F priority).Ramsey :=
  fullBlockReadoutExpansion_ramsey (Γ) B.homogeneous priority
    (actual_block_readout_ramsey B ht F priority)

theorem actual_full_block_readout_reasonable :
    (actualFullBlockReadoutData B ht F priority).Reasonable :=
  fullBlockReadoutExpansion_reasonable (Γ) B.homogeneous priority

/-- Joint embeddings retain the same full code. Normalize only the
host order and read back the already constructed actual full maps. -/
theorem actual_full_block_readout_jep :
    ExpandedJEP (actualFullBlockReadoutData B ht F priority) := by
  intro A E a b
  obtain ⟨J,c,⟨l⟩,⟨r⟩⟩ := actual_full_readout_jep B ht F A E a.val b.val
  refine ⟨J,normalizeActualReadout B ht F priority c,?_,?_⟩
  · exact ⟨readoutToFullBlock (Γ) B.homogeneous priority
      (normalizeActualReadoutEmbedding B ht F priority a c
        ((Γ).relationalToReadout B.homogeneous l))⟩
  · exact ⟨readoutToFullBlock (Γ) B.homogeneous priority
      (normalizeActualReadoutEmbedding B ht F priority b c
        ((Γ).relationalToReadout B.homogeneous r))⟩

end
end CCO.UnfilteredEP
