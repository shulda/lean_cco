import CCO.APRamseyReadout.Templates
import CCO.APRamseyReadout.TemplateBounds
import CCO.FullCode.Cofinality

/-! C35--C40: coordinate completion on the SAME ambient host.
The carrier is a subset of the original literal tagged roots, so strict
idempotence is equality of root sets, not an isomorphism of chosen hosts.
No Ramsey, EP, cofinality or original algebraic-closure premise enters. -/

universe u v w z a b c
namespace CCO.APRamseyReadout
open CCO.FullCode
noncomputable section

variable {L : Language.{u}} {V : Type v} {W : Type w} {Z : Type z}
variable {C : Structure L V} {D : Structure L W} {E : Structure L Z}
variable {S : RootScheme L} {A : Type a} {B : Type b} {K : Type c}

def completionRoots (O : Object C S A) : Set (Root C S) :=
  {r | ∀ j, r.coordinate j ∈ O.support}

def completionObject (O : Object C S A) : Object C S (completionRoots O) where
  root := Subtype.val
  injective := Subtype.val_injective

def selectedRoot (O : Object C S A) (x : A) : completionRoots O :=
  ⟨O.root x,O.coordinate_mem_support x⟩

def selectedEmbedding (N : NormalForms L) (O : Object C S A) :
    Object.Embedding N O (completionObject O) where
  point := selectedRoot O
  injective := fun x y h => O.injective (congrArg Subtype.val h)
  tag_eq _ := rfl
  equality_iff _ _ _ _ := Iff.rfl
  unary_iff _ _ _ := Iff.rfl
  binary_iff _ _ _ _ _ := Iff.rfl

theorem completion_support (O : Object C S A) :
    (completionObject O).support = O.support := by
  apply Set.Subset.antisymm
  · apply C.closure_minimal (C.isClosed_closure O.coordinates)
    rintro y ⟨r,j,rfl⟩
    exact r.property j
  · apply C.closure_minimal (C.isClosed_closure (completionObject O).coordinates)
    rintro y ⟨x,j,rfl⟩
    exact C.subset_closure _ ⟨selectedRoot O x,j,rfl⟩

theorem completion_idempotent (O : Object C S A) :
    completionRoots (completionObject O) = completionRoots O := by
  ext r
  change (∀ j, r.coordinate j ∈ (completionObject O).support) ↔
    ∀ j, r.coordinate j ∈ O.support
  rw [completion_support]

/-- Restricting and reincluding the SAME literal tuple gives the
canonical support view, without an arbitrary new tuple representative. -/
def completionRootEquiv (O : Object C S A) :
    completionRoots O ≃ Root O.supportStructure S where
  toFun r := r.val.restrict (C.isClosed_closure O.coordinates) r.property
  invFun r := ⟨r.map (C.inclusion O.support (C.isClosed_closure O.coordinates)),
    fun j => (r.coordinate j).property⟩
  left_inv r := Subtype.ext (Root.map_restrict _ _ _)
  right_inv r := by
    apply Root.ext_coordinates rfl
    intro j
    exact Subtype.ext rfl

@[simp] theorem completionRootEquiv_map (O : Object C S A) (r : completionRoots O) :
    (completionRootEquiv O r).map (C.inclusion O.support (C.isClosed_closure O.coordinates)) =
      r.val := Root.map_restrict _ _ _

def completionToSupport (N : NormalForms L) (O : Object C S A) :
    Object.Embedding N (completionObject O) (Object.full O.supportStructure S) where
  point := completionRootEquiv O
  injective := (completionRootEquiv O).injective
  tag_eq _ := rfl
  equality_iff r s p q := by
    have h := equalityCode_map N (C.inclusion O.support (C.isClosed_closure O.coordinates))
      (completionRootEquiv O r) (completionRootEquiv O s) p q
    rw [completionRootEquiv_map,completionRootEquiv_map] at h
    exact h.symm
  unary_iff U r p := by
    have h := unaryCode_map N (C.inclusion O.support (C.isClosed_closure O.coordinates))
      U (completionRootEquiv O r) p
    rw [completionRootEquiv_map] at h
    exact h.symm
  binary_iff R r s p q := by
    have h := binaryCode_map N (C.inclusion O.support (C.isClosed_closure O.coordinates))
      R (completionRootEquiv O r) (completionRootEquiv O s) p q
    rw [completionRootEquiv_map,completionRootEquiv_map] at h
    exact h.symm

def completionFromSupport (N : NormalForms L) (O : Object C S A) :
    Object.Embedding N (Object.full O.supportStructure S) (completionObject O) where
  point := (completionRootEquiv O).symm
  injective := (completionRootEquiv O).symm.injective
  tag_eq _ := rfl
  equality_iff r s p q := equalityCode_map N
    (C.inclusion O.support (C.isClosed_closure O.coordinates)) r s p q
  unary_iff U r p := unaryCode_map N
    (C.inclusion O.support (C.isClosed_closure O.coordinates)) U r p
  binary_iff R r s p q := binaryCode_map N
    (C.inclusion O.support (C.isClosed_closure O.coordinates)) R r s p q

noncomputable def completionEmbedding {N : NormalForms L}
    {O : Object C S A} {P : Object D S B} (f : Object.Embedding N O P)
    (hC : N.Valid C) (hD : N.Valid D) :
    Object.Embedding N (completionObject O) (completionObject P) :=
  (completionFromSupport N P).comp
    ((Object.rootEmbedding N (Object.full O.supportStructure S) (f.onSupport hC hD)).comp
      (completionToSupport N O))

theorem completionEmbedding_selected {N : NormalForms L}
    {O : Object C S A} {P : Object D S B} (f : Object.Embedding N O P)
    (hC : N.Valid C) (hD : N.Valid D) (x : A) :
    (completionEmbedding f hC hD).point (selectedRoot O x) = selectedRoot P (f.point x) := by
  apply Subtype.ext
  apply Root.ext_coordinates (f.tag_eq x).symm
  intro j
  exact f.extendPoint_coordinate hC hD x j

theorem completionEmbedding_id {N : NormalForms L} (O : Object C S A) (hC : N.Valid C) :
    completionEmbedding (Object.Embedding.id N O) hC hC =
      Object.Embedding.id N (completionObject O) := by
  apply Object.Embedding.ext
  intro r
  apply Subtype.ext
  refine Root.ext_coordinates
    (r := ((completionEmbedding (Object.Embedding.id N O) hC hC).point r).val)
    (s := r.val) (by rfl) ?_
  intro j
  change (((Object.Embedding.id N O).onSupport hC hC).point
    ⟨r.val.coordinate j,r.property j⟩).val = r.val.coordinate j
  rw [Object.onSupport_id]
  rfl

theorem completionEmbedding_comp {N : NormalForms L}
    {O : Object C S A} {P : Object D S B} {Q : Object E S K}
    (f : Object.Embedding N O P) (g : Object.Embedding N P Q)
    (hC : N.Valid C) (hD : N.Valid D) (hE : N.Valid E) :
    completionEmbedding (g.comp f) hC hE =
      (completionEmbedding g hD hE).comp (completionEmbedding f hC hD) := by
  apply Object.Embedding.ext
  intro r
  apply Subtype.ext
  refine Root.ext_coordinates
    (r := ((completionEmbedding (g.comp f) hC hE).point r).val)
    (s := (((completionEmbedding g hD hE).comp (completionEmbedding f hC hD)).point r).val)
    (by rfl) ?_
  intro j
  change (((g.comp f).onSupport hC hE).point ⟨r.val.coordinate j,r.property j⟩).val =
    ((g.onSupport hD hE).point ((f.onSupport hC hD).point
      ⟨r.val.coordinate j,r.property j⟩)).val
  rw [Object.onSupport_comp]
  rfl

def completionIdempotentEquiv (O : Object C S A) :
    completionRoots (completionObject O) ≃ completionRoots O where
  toFun r := ⟨r.val,by simpa only [completion_idempotent O] using r.property⟩
  invFun r := ⟨r.val,by simpa only [completion_idempotent O] using r.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def completionSecondEmbedding (N : NormalForms L) (O : Object C S A) :
    Object.Embedding N (completionObject (completionObject O)) (completionObject O) where
  point := completionIdempotentEquiv O
  injective := (completionIdempotentEquiv O).injective
  tag_eq _ := rfl
  equality_iff _ _ _ _ := Iff.rfl
  unary_iff _ _ _ := Iff.rfl
  binary_iff _ _ _ _ _ := Iff.rfl

/-- After the proved equality of root sets, the entire full code is
literally unchanged. The displayed equivalence only casts membership. -/
theorem completion_code_idempotent (N : NormalForms L) (O : Object C S A) :
    (completionObject (completionObject O)).codeStructure N =
      ((completionObject O).codeStructure N).comapEquiv (completionIdempotentEquiv O) :=
  (completionSecondEmbedding N O).asCodeEmbedding.source_eq_of_same_point
    (((completionObject O).codeStructure N).comapEquivEmbedding (completionIdempotentEquiv O))
    (fun _ => rfl)

noncomputable def completionCodeEmbedding (N : NormalForms L)
    (O : Object C S A) (P : Object D S B) (hC : N.Valid C) (hD : N.Valid D)
    (f : Structure.Embedding (O.codeStructure N) (P.codeStructure N)) :
    Structure.Embedding ((completionObject O).codeStructure N)
      ((completionObject P).codeStructure N) :=
  (completionEmbedding (Object.embeddingOfCode f) hC hD).asCodeEmbedding

theorem completionCodeEmbedding_selected (N : NormalForms L)
    (O : Object C S A) (P : Object D S B) (hC : N.Valid C) (hD : N.Valid D)
    (f : Structure.Embedding (O.codeStructure N) (P.codeStructure N)) (x : A) :
    (completionCodeEmbedding N O P hC hD f).point (selectedRoot O x) =
      selectedRoot P (f.point x) :=
  completionEmbedding_selected (Object.embeddingOfCode f) hC hD x

theorem completion_size_bounds (N : NormalForms L) (O : Object C S A) [Finite A]
    (hC : N.Valid C) :
    Nat.card O.support ≤ Nat.card (Presentation N S) * Nat.card A ∧
      Nat.card (completionRoots O) ≤ rootTupleBound S (Nat.card O.support) := by
  haveI : Finite O.support := (O.support_finite N hC).to_subtype
  refine ⟨template_card_bound N O hC,?_⟩
  rw [Nat.card_congr (completionRootEquiv O)]
  exact root_card_bound O.supportStructure S

/-- In the concrete selected-MI application positive arity is proved
from its nonempty family, rather than asserted for arbitrary schemes. -/
theorem completion_empty_of_positive (O : Object C S A) [IsEmpty A]
    (positive : ∀ s, 0 < S.arity s) : completionRoots O = ∅ := by
  have hcoordinates : O.coordinates = ∅ := by
    ext y
    constructor
    · rintro ⟨x,j,hj⟩
      exact isEmptyElim x
    · intro h
      exact False.elim h
  have hsupport : O.support = ∅ := by
    ext y
    change (∃ x ∈ O.coordinates, Relation.ReflTransGen C.Step x y) ↔ False
    rw [hcoordinates]
    simp
  ext r
  constructor
  · intro hr
    have h := hr ⟨0,positive r.tag⟩
    rw [hsupport] at h
    exact h
  · intro h
    exact False.elim h

end
end CCO.APRamseyReadout
