import CCO.APRamseyReadout.TuplePredicates
import CCO.TerminalHiddenHN.RealExpansion
import CCO.FullCode.CodeLanguage

/-! A finite typed relational readout of all marked tuple-term codes.
The only variable datum is the order on the entire generated support.
Every restriction and expanded embedding retains the same original map.
The Ramsey application is separate from this finite reasonable witness. -/

universe u v w r l k
namespace CCO.APRamseyReadout.TupleInterpretation
open CCO.FullCode
noncomputable section
variable {ι : Type u} {X : ι → Type v}
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable {L : Language.{l}} {V : Type k}
variable {S : CCO.AtomicSource.{u,v,w} ι X} {C : Structure L V} {scheme : RootScheme L}
variable (D : TupleInterpretation (G := G) S C scheme)

/-- FullCode's relational carrier has one bookkeeping sort. The actual
added predicate names explicitly remember their original input sorts. -/
abbrev FullUnaryName := Σ i : ι, (codeLanguage D.normal scheme).Unary
abbrev FullBinaryName := Σ i : ι, Σ j : ι,
  (codeLanguage D.normal scheme).Binary ⊕
    (Presentation D.normal scheme × Presentation D.normal scheme)

def fullUnary {A : CCO.FiniteInduced (X := X)} (_a : D.ReadoutOn A)
    (q : D.FullUnaryName) (x : A.vertices) : Prop :=
  x.val.1 = q.1 ∧ ((D.object A).codeStructure D.normal).unary q.2 x

def fullBinary {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A)
    (q : D.FullBinaryName) (x y : A.vertices) : Prop :=
  x.val.1 = q.1 ∧ y.val.1 = q.2.1 ∧
    match q.2.2 with
    | .inl R => ((D.object A).codeStructure D.normal).binary R x y
    | .inr pq => D.TermOrder a x y pq.1 pq.2

private theorem fullUnary_embedding (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : D.ReadoutEmbedding H a b) (q : D.FullUnaryName) (x : A.vertices) :
    D.fullUnary b q (f.old.toEmbedding x) ↔ D.fullUnary a q x := by
  change ((f.old.toEmbedding x).val.1 = q.1 ∧ _) ↔ (x.val.1 = q.1 ∧ _)
  rw [f.old.preserves_sort x]
  exact and_congr Iff.rfl ((D.codeEmbedding H f.old).asCodeEmbedding.unary_iff q.2 x)

private theorem fullBinary_embedding (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : D.ReadoutEmbedding H a b) (q : D.FullBinaryName) (x y : A.vertices) :
    D.fullBinary b q (f.old.toEmbedding x) (f.old.toEmbedding y) ↔ D.fullBinary a q x y := by
  rcases q with ⟨i,j,q⟩
  change ((f.old.toEmbedding x).val.1 = i ∧ (f.old.toEmbedding y).val.1 = j ∧ _) ↔
    (x.val.1 = i ∧ y.val.1 = j ∧ _)
  rw [f.old.preserves_sort x,f.old.preserves_sort y]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  cases q with
  | inl R => exact (D.codeEmbedding H f.old).asCodeEmbedding.binary_iff R x y
  | inr pq => exact D.termOrder_embedding H f x y pq.1 pq.2

/-- The full finite comparison data determine the order on every
support point, including values shared by different roots. -/
theorem full_readout_faithful {A : CCO.FiniteInduced (X := X)} (a b : D.ReadoutOn A)
    (h : ∀ q x y, D.fullBinary a q x y ↔ D.fullBinary b q x y) : a = b := by
  apply D.termOrder_faithful a b
  intro x y p q
  have hh := h ⟨x.val.1,y.val.1,.inr ⟨p,q⟩⟩ x y
  exact ⟨fun hp => (hh.mp ⟨rfl,rfl,hp⟩).2.2,
    fun hp => (hh.mpr ⟨rfl,rfl,hp⟩).2.2⟩

/-- Finite predicates on the ORIGINAL finite induced objects. All
non-order codes and all same-root/cross-root comparisons are retained. -/
def fullReadoutExpansion (H : CCO.HomogeneousSource S G) :
    CCO.TerminalHiddenHN.RealExpansionData.{u,v,w,max u l,k} S where
  Unary := D.FullUnaryName
  Binary := D.FullBinaryName
  finiteUnary := by letI := S.finiteSort; infer_instance
  finiteBinary := by letI := S.finiteSort; infer_instance
  unarySort q := q.1
  leftSort q := q.1
  rightSort q := q.2.1
  Expansion := D.ReadoutOn
  nonempty := D.readout_nonempty
  unary := D.fullUnary
  binary := D.fullBinary
  unary_sorted a q x h := h.1
  binary_sorted a q x y h := ⟨h.1,h.2.1⟩
  faithful a b _hu hb := D.full_readout_faithful a b hb
  restrict e b := D.restrictReadout H e b
  restrict_unary e b q x :=
    (D.fullUnary_embedding H (D.restrictReadoutEmbedding H e b) q x).symm
  restrict_binary e b q x y :=
    (D.fullBinary_embedding H (D.restrictReadoutEmbedding H e b) q x y).symm

theorem fullReadoutExpansion_precompact (H : CCO.HomogeneousSource S G)
    (A : CCO.FiniteInduced (X := X)) :
    Finite ((D.fullReadoutExpansion H).Expansion A) :=
  (D.fullReadoutExpansion H).finite_expansions A

theorem fullReadoutExpansion_reasonable (H : CCO.HomogeneousSource S G) :
    (D.fullReadoutExpansion H).Reasonable := by
  intro A B e a
  exact D.readout_reasonable H e a

/-- Finite-table embeddings recover exactly their canonical ordered
support extension, without an inverse for arbitrary unmarked hidden maps. -/
def relationalToReadout (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (e : (D.fullReadoutExpansion H).Embedding a b) : D.ReadoutEmbedding H a b :=
  D.readoutEmbedding_of_termOrders H e.old (by
    intro x y p q
    have hh := e.binary_iff ⟨x.val.1,y.val.1,.inr ⟨p,q⟩⟩ x y
    exact ⟨fun hp => (hh.mp ⟨e.old.preserves_sort x,e.old.preserves_sort y,hp⟩).2.2,
      fun hp => (hh.mpr ⟨rfl,rfl,hp⟩).2.2⟩)

def readoutToRelational (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : D.ReadoutEmbedding H a b) : (D.fullReadoutExpansion H).Embedding a b where
  old := f.old
  unary_iff q x := D.fullUnary_embedding H f q x
  binary_iff q x y := D.fullBinary_embedding H f q x y

def relationalReadoutEquiv (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A) (b : D.ReadoutOn B) :
    (D.fullReadoutExpansion H).Embedding a b ≃ D.ReadoutEmbedding H a b where
  toFun := D.relationalToReadout H
  invFun := D.readoutToRelational H
  left_inv f := by
    apply CCO.TerminalHiddenHN.RealExpansionData.Embedding.ext
    intro x
    rfl
  right_inv f := by
    apply ReadoutEmbedding.ext H
    intro x
    rfl

theorem readoutToRelational_comp (H : CCO.HomogeneousSource S G)
    {A B E : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B} {c : D.ReadoutOn E}
    (g : D.ReadoutEmbedding H b c) (f : D.ReadoutEmbedding H a b) :
    D.readoutToRelational H (g.comp H f) =
      (D.readoutToRelational H g).comp (D.readoutToRelational H f) := by
  apply CCO.TerminalHiddenHN.RealExpansionData.Embedding.ext
  intro x
  rfl

end
end CCO.APRamseyReadout.TupleInterpretation
