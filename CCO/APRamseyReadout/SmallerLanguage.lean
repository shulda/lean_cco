import CCO.APRamseyReadout.SortBlockNormalizer
import CCO.APRamseyReadout.ProperHiddenAge
import CCO.APRamseyReadout.CoordinateBridge
import CCO.APRamseyReadout.TupleReadout
import CCO.TerminalHiddenHN.FiniteOrderExtension
import CCO.FullCode.Consumer
import Mathlib.Basic.Finite.Sum
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sigma

/-! Block codes retain within-HIDDEN-target comparisons. Different
visible tags are irrelevant to this criterion. The omitted comparisons
are reconstructed from actual presentation domains and fixed sort priority. -/

universe u v w a b r l k
namespace CCO.APRamseyReadout
open CCO.FullCode
noncomputable section
variable {L : Language.{u}} {V : Type v} {W : Type w}
variable (priority : LinearOrder L.Sorts)
variable {C : Structure (blockLanguage L) V} {D : Structure (blockLanguage L) W}
variable {S : RootScheme (blockLanguage L)} (N : NormalForms (blockLanguage L))

/-- Presentation output sorts constrain EVERY literal order symbol. -/
theorem blockOrderCode_sorts (r s : Root C S) (p q : Presentation N S)
    (i j : L.Sorts) (h : BinaryCode N (.inr (i,j)) r s p q) : p.2.1 = i ∧ q.2.1 = j := by
  obtain ⟨x,y,hx,hy,hxy⟩ := h
  have hs := C.binary_sorted (.inr (i,j)) x y hxy
  exact ⟨(r.presentation_sorted N p hx).symm.trans hs.1,
    (s.presentation_sorted N q hy).symm.trans hs.2⟩

/-- Applicability is explicit: a missing term presentation makes the
comparison false even when the priority orders its target sorts. -/
theorem blockOrderCode_different (fixed : blockNormalize L priority C = C)
    (r s : Root C S) (p q : Presentation N S) (i j : L.Sorts) (hne : i ≠ j) :
    BinaryCode N (.inr (i,j)) r s p q ↔
      (r.presentation N p).Nonempty ∧ (s.presentation N q).Nonempty ∧
        p.2.1 = i ∧ q.2.1 = j ∧ @LT.lt _ priority.toLT i j := by
  constructor
  · rintro ⟨x,y,hx,hy,hxy⟩
    have ht := blockOrderCode_sorts N r s p q i j ⟨x,y,hx,hy,hxy⟩
    have hb : (blockNormalize L priority C).binary (.inr (i,j)) x y := fixed.symm ▸ hxy
    change C.sort x = i ∧ C.sort y = j ∧
      (@LT.lt _ priority.toLT i j ∨ (i = j ∧ C.binary (.inr (i,j)) x y)) at hb
    exact ⟨⟨x,hx⟩,⟨y,hy⟩,ht.1,ht.2,hb.2.2.elim id (fun h => False.elim (hne h.1))⟩
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩,hi,hj,hpriority⟩
    refine ⟨x,y,hx,hy,?_⟩
    have hb : (blockNormalize L priority C).binary (.inr (i,j)) x y :=
      ⟨(r.presentation_sorted N p hx).trans hi,(s.presentation_sorted N q hy).trans hj,
        Or.inl hpriority⟩
    exact fixed ▸ hb

/-- The reduced tests keep every non-order code. The final actual owner
reduction deletes those through their proved old-type definitions. -/
structure WithinTargetEmbedding {A : Type a} {B : Type b}
    (O : Object C S A) (P : Object D S B) where
  point : A → B
  injective : Function.Injective point
  tag_eq : ∀ x, (P.root (point x)).tag = (O.root x).tag
  equality_iff : ∀ x y p q, EqualityCode N (P.root (point x)) (P.root (point y)) p q ↔
    EqualityCode N (O.root x) (O.root y) p q
  unary_iff : ∀ U x p, UnaryCode N U (P.root (point x)) p ↔ UnaryCode N U (O.root x) p
  old_binary_iff : ∀ R x y p q, BinaryCode N (.inl R) (P.root (point x)) (P.root (point y)) p q ↔
    BinaryCode N (.inl R) (O.root x) (O.root y) p q
  within_iff : ∀ i x y p q, BinaryCode N (.inr (i,i)) (P.root (point x)) (P.root (point y)) p q ↔
    BinaryCode N (.inr (i,i)) (O.root x) (O.root y) p q

namespace WithinTargetEmbedding
variable {N} {A : Type a} {B : Type b} {O : Object C S A} {P : Object D S B}

@[ext] theorem ext {f g : WithinTargetEmbedding N O P} (h : ∀ x, f.point x = g.point x) : f = g := by
  cases f; cases g
  have hp := funext h
  cases hp
  rfl

def ofFull (f : Object.Embedding N O P) : WithinTargetEmbedding N O P where
  point := f.point
  injective := f.injective
  tag_eq := f.tag_eq
  equality_iff := f.equality_iff
  unary_iff := f.unary_iff
  old_binary_iff R := f.binary_iff (.inl R)
  within_iff i := f.binary_iff (.inr (i,i))

/-- Every omitted unequal-output-sort test is restored by definedness
and priority. Both directions hold on ALL visible embedding maps. -/
def toFull (fixedC : blockNormalize L priority C = C) (fixedD : blockNormalize L priority D = D)
    (f : WithinTargetEmbedding N O P) : Object.Embedding N O P where
  point := f.point
  injective := f.injective
  tag_eq := f.tag_eq
  equality_iff := f.equality_iff
  unary_iff := f.unary_iff
  binary_iff R x y p q := by
    cases R with
    | inl R => exact f.old_binary_iff R x y p q
    | inr ij =>
      obtain ⟨i,j⟩ := ij
      by_cases he : i = j
      · subst j
        exact f.within_iff i x y p q
      · rw [blockOrderCode_different priority N fixedD,blockOrderCode_different priority N fixedC]
        · have hp : ((P.root (f.point x)).presentation N p).Nonempty ↔
              ((O.root x).presentation N p).Nonempty := by
            rw [← definedness_diagonal N (P.root (f.point x)) p,
              ← definedness_diagonal N (O.root x) p]
            exact f.equality_iff x x p p
          have hq : ((P.root (f.point y)).presentation N q).Nonempty ↔
              ((O.root y).presentation N q).Nonempty := by
            rw [← definedness_diagonal N (P.root (f.point y)) q,
              ← definedness_diagonal N (O.root y) q]
            exact f.equality_iff y y q q
          exact and_congr hp (and_congr hq Iff.rfl)
        · exact he
        · exact he

end WithinTargetEmbedding

/-- Same point maps, with no surjectivity-on-maps or chosen subfamily
of code embeddings hidden in the reduction. -/
def withinTargetEmbeddingEquiv {A : Type a} {B : Type b}
    (O : Object C S A) (P : Object D S B)
    (fixedC : blockNormalize L priority C = C) (fixedD : blockNormalize L priority D = D) :
    WithinTargetEmbedding N O P ≃ Object.Embedding N O P where
  toFun := WithinTargetEmbedding.toFull priority fixedC fixedD
  invFun := WithinTargetEmbedding.ofFull
  left_inv _ := WithinTargetEmbedding.ext (fun _ => rfl)
  right_inv _ := Object.Embedding.ext (fun _ => rfl)


abbrev WithinPresentationPair := {pq : Presentation N S × Presentation N S // pq.1.2.1 = pq.2.2.1}

/-- A literal finite relational code, retaining non-order tests and
ONLY comparisons whose presentation OUTPUT sorts agree. -/
def withinCodeLanguage : Language.{u} where
  Sorts := PUnit
  Func := PEmpty
  Unary := (codeLanguage N S).Unary
  Binary := (Presentation N S × Presentation N S) ⊕
    (L.Binary × Presentation N S × Presentation N S) ⊕ WithinPresentationPair N (S := S)
  input F := PEmpty.elim F
  output F := PEmpty.elim F
  unarySort _ := PUnit.unit
  leftSort _ := PUnit.unit
  rightSort _ := PUnit.unit
  finiteSort := inferInstance
  finiteFunc := inferInstance
  finiteUnary := inferInstance
  finiteBinary := inferInstance

def withinCodeStructure {A : Type a} (O : Object C S A) : Structure (withinCodeLanguage N (S := S)) A where
  sort _ := PUnit.unit
  func F := PEmpty.elim F
  functional F := PEmpty.elim F
  func_sorted F := PEmpty.elim F
  unary := (O.codeStructure N).unary
  unary_sorted _ _ _ := rfl
  binary R x y := match R with
    | .inl pq => EqualityCode N (O.root x) (O.root y) pq.1 pq.2
    | .inr (.inl rpq) => BinaryCode N (.inl rpq.1) (O.root x) (O.root y) rpq.2.1 rpq.2.2
    | .inr (.inr pq) => BinaryCode N (.inr (pq.val.1.2.1,pq.val.1.2.1))
      (O.root x) (O.root y) pq.val.1 pq.val.2
  binary_sorted _ _ _ _ := ⟨rfl,rfl⟩

namespace WithinTargetEmbedding
variable {N} {A : Type a} {B : Type b} {O : Object C S A} {P : Object D S B}

def asCodeEmbedding (f : WithinTargetEmbedding N O P) :
    Structure.Embedding (withinCodeStructure N O) (withinCodeStructure N P) where
  point := f.point
  injective := f.injective
  sort_eq _ := rfl
  map_func F := PEmpty.elim F
  reflect_func F := PEmpty.elim F
  unary_iff U x := by
    cases U with
    | inl tag =>
      change (P.root (f.point x)).tag = tag ↔ (O.root x).tag = tag
      rw [f.tag_eq]
    | inr Up => exact f.unary_iff Up.1 x Up.2
  binary_iff R x y := by
    cases R with
    | inl pq => exact f.equality_iff x y pq.1 pq.2
    | inr R =>
      cases R with
      | inl rpq => exact f.old_binary_iff rpq.1 x y rpq.2.1 rpq.2.2
      | inr pq => exact f.within_iff pq.val.1.2.1 x y pq.val.1 pq.val.2

end WithinTargetEmbedding

def withinEmbeddingOfCode {A : Type a} {B : Type b} {O : Object C S A} {P : Object D S B}
    (f : Structure.Embedding (withinCodeStructure N O) (withinCodeStructure N P)) :
    WithinTargetEmbedding N O P where
  point := f.point
  injective := f.injective
  tag_eq x := (f.unary_iff (.inl (O.root x).tag) x).mpr rfl
  equality_iff x y p q := f.binary_iff (.inl (p,q)) x y
  unary_iff U x p := f.unary_iff (.inr (U,p)) x
  old_binary_iff R x y p q := f.binary_iff (.inr (.inl (R,p,q))) x y
  within_iff i x y p q := by
    by_cases hp : p.2.1 = i
    · by_cases hq : q.2.1 = i
      · let pair : WithinPresentationPair N (S := S) := ⟨(p,q),hp.trans hq.symm⟩
        have hh := f.binary_iff (.inr (.inr pair)) x y
        change BinaryCode N (.inr (p.2.1,p.2.1)) (P.root (f.point x)) (P.root (f.point y)) p q ↔
          BinaryCode N (.inr (p.2.1,p.2.1)) (O.root x) (O.root y) p q at hh
        simpa only [hp] using hh
      · constructor
        · intro h
          exact False.elim (hq (blockOrderCode_sorts N _ _ p q i i h).2)
        · intro h
          exact False.elim (hq (blockOrderCode_sorts N _ _ p q i i h).2)
    · constructor
      · intro h
        exact False.elim (hp (blockOrderCode_sorts N _ _ p q i i h).1)
      · intro h
        exact False.elim (hp (blockOrderCode_sorts N _ _ p q i i h).1)

def withinCodeEmbeddingEquiv {A : Type a} {B : Type b} (O : Object C S A) (P : Object D S B) :
    WithinTargetEmbedding N O P ≃ Structure.Embedding (withinCodeStructure N O) (withinCodeStructure N P) where
  toFun := WithinTargetEmbedding.asCodeEmbedding
  invFun := withinEmbeddingOfCode priority N
  left_inv _ := WithinTargetEmbedding.ext (fun _ => rfl)
  right_inv _ := Structure.Embedding.ext (fun _ => rfl)

/-- The finite same-target language and the full block language have
EXACTLY the same induced embedding maps on fixed block objects. -/
def withinFullCodeEmbeddingEquiv {A : Type a} {B : Type b}
    (O : Object C S A) (P : Object D S B)
    (fixedC : blockNormalize L priority C = C) (fixedD : blockNormalize L priority D = D) :
    Structure.Embedding (withinCodeStructure N O) (withinCodeStructure N P) ≃
      Structure.Embedding (O.codeStructure N) (P.codeStructure N) :=
  (withinCodeEmbeddingEquiv priority N O P).symm.trans
    ((withinTargetEmbeddingEquiv priority N O P fixedC fixedD).trans (O.codeEmbeddingEquiv N P))


/-- Extend every prescribed within-sort order on the SAME old image,
then concatenate. Normalizing an arbitrary global extension preserves
each such within-sort extension and fixes the old block source exactly. -/
theorem block_order_extension {I : Type u} {X : Type v} {Y : Type w} [Finite Y]
    (priority : LinearOrder I) (sortX : X → I) (sortY : Y → I) (old : LinearOrder X)
    (fixed : sortBlockOrder sortX priority old = old) (f : X → Y) (hf : Function.Injective f)
    (hs : ∀ x, sortY (f x) = sortX x) :
    ∃ o : LinearOrder Y, sortBlockOrder sortY priority o = o ∧
      ∀ x y, @LT.lt _ o.toLT (f x) (f y) ↔ @LT.lt _ old.toLT x y := by
  letI := old
  obtain ⟨o,ho⟩ := CCO.TerminalHiddenHN.finite_linearOrder_extension f hf
  refine ⟨sortBlockOrder sortY priority o,sortBlockOrder_idempotent _ _ _,?_⟩
  intro x y
  have h := sortBlockOrder_map_iff sortX sortY priority old o f hs ho x y
  exact h.trans (Iff.of_eq (congrArg (fun a : LinearOrder X => @LT.lt _ a.toLT x y) fixed))

end

section Actual
open CCO.CloneTupleGeometry
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- The two alphabets have literally the same symbols and point maps.
Only definitional presentations of their sort-field functions differ. -/
def coordinateBlockReduct : Reduct (blockLanguage (CoordinateLanguage B ht)) (OrderedCoordinateLanguage B ht) where
  sortMap s := s
  funcMap F := F
  unaryMap U := U
  binaryMap R := R
  input_eq _ := rfl
  output_eq _ := rfl
  unary_eq U := PEmpty.elim U
  left_eq R := by cases R <;> rfl
  right_eq R := by cases R <;> rfl

def coordinateOrderedReduct : Reduct (OrderedCoordinateLanguage B ht) (blockLanguage (CoordinateLanguage B ht)) where
  sortMap s := s
  funcMap F := F
  unaryMap U := U
  binaryMap R := R
  input_eq _ := rfl
  output_eq _ := rfl
  unary_eq U := PEmpty.elim U
  left_eq R := by cases R <;> rfl
  right_eq R := by cases R <;> rfl

@[simp] theorem coordinateOrdered_block {Y : Type a} (C : Structure (OrderedCoordinateLanguage B ht) Y) :
    (C.reduct (coordinateBlockReduct B ht)).reduct (coordinateOrderedReduct B ht) = C := by cases C; rfl

@[simp] theorem coordinateBlock_ordered {Y : Type a} (C : Structure (blockLanguage (CoordinateLanguage B ht)) Y) :
    (C.reduct (coordinateOrderedReduct B ht)).reduct (coordinateBlockReduct B ht) = C := by cases C; rfl

private theorem coordinateOrdered_structure {Y : Type a}
    (C : CCO.UnarySupport.Structure (Sig B ht) Y) (o : LinearOrder Y) :
    (blockStructure (CoordinateLanguage B ht) (CoordinateModel B ht C) o).reduct (coordinateOrderedReduct B ht) =
      @OrderedCoordinateModel B ht Y C o := by
  refine TerminalHiddenHN.fullStructure_ext
    (C := (blockStructure (CoordinateLanguage B ht) (CoordinateModel B ht C) o).reduct
      (coordinateOrderedReduct B ht)) (D := @OrderedCoordinateModel B ht Y C o) rfl rfl ?_ ?_
  · funext U
    exact PEmpty.elim U
  · funext R x y
    cases R <;> rfl

private theorem coordinateBlock_structure {Y : Type a}
    (C : CCO.UnarySupport.Structure (Sig B ht) Y) (o : LinearOrder Y) :
    (@OrderedCoordinateModel B ht Y C o).reduct (coordinateBlockReduct B ht) =
      blockStructure (CoordinateLanguage B ht) (CoordinateModel B ht C) o :=
  (congrArg (fun M => M.reduct (coordinateBlockReduct B ht))
    (coordinateOrdered_structure B ht C o)).symm

abbrev ProperCoordinateAge (D : FiniteHidden.{max u v w,a} (CoordinateLanguage B ht)) : Prop :=
  ActualAge B ht (TerminalHiddenHN.binaryDecode (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)) D.model) ∧
      ∀ x, ProperSort B ht (D.model.sort x)

def ProjectedProperBlockAge (A : FiniteHidden.{max u v w,a} (blockLanguage (CoordinateLanguage B ht))) : Prop :=
  ProperOrderedAge B ht ⟨A.Carrier,A.model.reduct (coordinateOrderedReduct B ht),A.finite⟩

/-- Exact all-carrier class identity, retaining EVERY proper hidden sort
and EVERY global order, through the same-symbol record bridge. -/
theorem allBlockOrders_proper :
    allBlockOrders (CoordinateLanguage B ht) (ProperCoordinateAge B ht) = ProjectedProperBlockAge.{u,v,w,a} B ht := by
  funext A
  apply propext
  constructor
  · rintro ⟨C,o,⟨hC,hproper⟩,he⟩
    let raw := TerminalHiddenHN.binaryDecode (Sig B ht)
      (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)) C
    refine ⟨⟨raw,o,hC,?_⟩,?_⟩
    · have hc := TerminalHiddenHN.binaryStructure_binaryDecode (Sig B ht)
        (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)) C
      exact (congrArg (fun M => M.reduct (coordinateOrderedReduct B ht)) he).trans
        ((congrArg (fun M => (blockStructure (CoordinateLanguage B ht) M o).reduct (coordinateOrderedReduct B ht)) hc.symm).trans
          (coordinateOrdered_structure B ht raw o))
    · intro x
      have hx := congrArg (fun M => M.sort x) he
      exact hx.symm ▸ hproper x
  · rintro ⟨⟨C,o,hC,he⟩,hproper⟩
    refine ⟨CoordinateModel B ht C,o,⟨?_,?_⟩,?_⟩
    · exact (TerminalHiddenHN.binaryDecode_binaryStructure (Sig B ht)
        (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)) C).symm ▸ hC
    · intro x
      have hx := congrArg (fun M => M.sort x) he
      exact hx ▸ hproper x
    · have hh := congrArg (fun M => M.reduct (coordinateBlockReduct B ht)) he
      exact (coordinateBlock_ordered B ht A.model).symm.trans
        (hh.trans (coordinateBlock_structure B ht C o))

private theorem projected_proper_ramsey : HasHiddenRamsey (ProjectedProperBlockAge.{u,v,w,a} B ht) := by
  intro A D hA hD n hn
  let Ao : FiniteHidden (OrderedCoordinateLanguage B ht) :=
    ⟨A.Carrier,A.model.reduct (coordinateOrderedReduct B ht),A.finite⟩
  let Do : FiniteHidden (OrderedCoordinateLanguage B ht) :=
    ⟨D.Carrier,D.model.reduct (coordinateOrderedReduct B ht),D.finite⟩
  obtain ⟨E,hE,arrow⟩ := proper_ordered_ramsey B ht Ao Do hA hD n hn
  refine ⟨⟨E.Carrier,E.model.reduct (coordinateBlockReduct B ht),E.finite⟩,?_,?_⟩
  · change ProperOrderedAge B ht ⟨E.Carrier,_,E.finite⟩
    rw [coordinateOrdered_block]
    exact hE
  · intro color
    obtain ⟨g,shade,hg⟩ := arrow (fun f => color (f.reduct (coordinateBlockReduct B ht)))
    refine ⟨g.reduct (coordinateBlockReduct B ht),shade,?_⟩
    intro f
    have he : (g.reduct (coordinateBlockReduct B ht)).comp f =
        (g.comp (f.reduct (coordinateOrderedReduct B ht))).reduct (coordinateBlockReduct B ht) :=
      Structure.Embedding.ext (fun _ => rfl)
    exact (congrArg color he).trans (hg (f.reduct (coordinateOrderedReduct B ht)))

def ProperBlockOrderedAge (priority : LinearOrder (CoordinateLanguage B ht).Sorts)
    (A : FiniteHidden.{max u v w,a} (OrderedCoordinateLanguage B ht)) : Prop :=
  ProperOrderedAge B ht A ∧ blockNormalize (CoordinateLanguage B ht) priority
    (A.model.reduct (coordinateBlockReduct B ht)) = A.model.reduct (coordinateBlockReduct B ht)

/-- Actual C50: every A04 field is supplied by the SAME whole proper
ordered age. The source output keeps its original ordered alphabet. -/
theorem proper_block_ordered_ramsey (priority : LinearOrder (CoordinateLanguage B ht).Sorts) :
    HasHiddenRamsey (ProperBlockOrderedAge.{u,v,w,a} B ht priority) := by
  have hh : FullHereditary (blockLanguage (CoordinateLanguage B ht))
      (allBlockOrders (CoordinateLanguage B ht) (ProperCoordinateAge.{u,v,w,a} B ht)) := by
    rw [allBlockOrders_proper B ht]
    intro A D hD e
    exact proper_ordered_of_embedding B ht hD (e.reduct (coordinateOrderedReduct B ht))
  have hr : HasHiddenRamsey (allBlockOrders (CoordinateLanguage B ht) (ProperCoordinateAge.{u,v,w,a} B ht)) := by
    rw [allBlockOrders_proper B ht]
    exact projected_proper_ramsey B ht
  have out := (sort_block_normalization (CoordinateLanguage B ht) priority
    (ProperCoordinateAge.{u,v,w,a} B ht) hh hr).2
  intro A D hA hD n hn
  let Ab : FiniteHidden (blockLanguage (CoordinateLanguage B ht)) :=
    ⟨A.Carrier,A.model.reduct (coordinateBlockReduct B ht),A.finite⟩
  let Db : FiniteHidden (blockLanguage (CoordinateLanguage B ht)) :=
    ⟨D.Carrier,D.model.reduct (coordinateBlockReduct B ht),D.finite⟩
  have hAb : blockFixedAge (CoordinateLanguage B ht) priority (ProperCoordinateAge B ht) Ab := by
    constructor
    · rw [allBlockOrders_proper B ht]
      change ProperOrderedAge B ht ⟨A.Carrier,_,A.finite⟩
      rw [coordinateOrdered_block]
      exact hA.1
    · exact hA.2
  have hDb : blockFixedAge (CoordinateLanguage B ht) priority (ProperCoordinateAge B ht) Db := by
    constructor
    · rw [allBlockOrders_proper B ht]
      change ProperOrderedAge B ht ⟨D.Carrier,_,D.finite⟩
      rw [coordinateOrdered_block]
      exact hD.1
    · exact hD.2
  obtain ⟨E,hE,arrow⟩ := out Ab Db hAb hDb n hn
  refine ⟨⟨E.Carrier,E.model.reduct (coordinateOrderedReduct B ht),E.finite⟩,?_,?_⟩
  · constructor
    · have hp := hE.1
      rw [allBlockOrders_proper B ht] at hp
      exact hp
    · exact hE.2
  · intro color
    obtain ⟨g,shade,hg⟩ := arrow (fun f => color (f.reduct (coordinateOrderedReduct B ht)))
    refine ⟨g.reduct (coordinateOrderedReduct B ht),shade,?_⟩
    intro f
    have he : (g.reduct (coordinateOrderedReduct B ht)).comp f =
        (g.comp (f.reduct (coordinateBlockReduct B ht))).reduct (coordinateOrderedReduct B ht) :=
      Structure.Embedding.ext (fun _ => rfl)
    exact (congrArg color he).trans (hg (f.reduct (coordinateBlockReduct B ht)))

end Actual

namespace TupleInterpretation
noncomputable section
variable {ι : Type u} {X : ι → Type v}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {L : Language.{l}} {Y : Type k} {C : Structure L Y} {scheme : RootScheme L}
variable {S : CCO.AtomicSource.{u,v,w} ι X}
variable (D : TupleInterpretation (G := G) S C scheme) (priority : LinearOrder L.Sorts)

/-- No arbitrary non-order bits: the datum is exactly one block order
on the entire selected root-generated support. -/
def BlockReadoutOn (A : CCO.FiniteInduced (X := X)) :=
  {a : D.ReadoutOn A // sortBlockOrder (D.supportStructure A).sort priority a.order = a.order}

def restrictBlockReadout (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (b : D.BlockReadoutOn priority B) : D.BlockReadoutOn priority A := by
  refine ⟨D.restrictReadout H e b.val,?_⟩
  apply LinearOrder.ext_lt
  intro x y
  have h := sortBlockOrder_map_iff (D.supportStructure A).sort (D.supportStructure B).sort priority
    (D.restrictReadout H e b.val).order b.val.order (D.supportEmbedding H e).point
      (D.supportEmbedding H e).sort_eq (fun _ _ => Iff.rfl) x y
  exact h.symm.trans (Iff.of_eq (congrArg (fun o : LinearOrder (D.support B) =>
    @LT.lt _ o.toLT ((D.supportEmbedding H e).point x) ((D.supportEmbedding H e).point y)) b.property))

def restrictBlockReadoutEmbedding (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (b : D.BlockReadoutOn priority B) :
    D.ReadoutEmbedding H (D.restrictBlockReadout priority H e b).val b.val :=
  D.restrictReadoutEmbedding H e b.val

theorem restrictBlockReadout_id (H : CCO.HomogeneousSource S G)
    {A : CCO.FiniteInduced (X := X)} (a : D.BlockReadoutOn priority A) :
    D.restrictBlockReadout priority H (oldId A) a = a :=
  Subtype.ext (D.restrictReadout_id H a.val)

theorem restrictBlockReadout_comp (H : CCO.HomogeneousSource S G)
    {A B E : CCO.FiniteInduced (X := X)} (g : CCO.InducedEmbedding S B E)
    (f : CCO.InducedEmbedding S A B) (c : D.BlockReadoutOn priority E) :
    D.restrictBlockReadout priority H (oldComp g f) c =
      D.restrictBlockReadout priority H f (D.restrictBlockReadout priority H g c) :=
  Subtype.ext (D.restrictReadout_comp H g f c.val)

theorem block_readout_nonempty (A : CCO.FiniteInduced (X := X)) : Nonempty (D.BlockReadoutOn priority A) := by
  let a := Classical.choice (D.readout_nonempty A)
  exact ⟨⟨⟨sortBlockOrder (D.supportStructure A).sort priority a.order⟩,
    sortBlockOrder_idempotent _ _ _⟩⟩

theorem block_readout_precompact (A : CCO.FiniteInduced (X := X)) : Finite (D.BlockReadoutOn priority A) := by
  letI : Finite (D.ReadoutOn A) := D.readout_precompact A
  exact inferInstanceAs (Finite {a : D.ReadoutOn A // sortBlockOrder (D.supportStructure A).sort priority a.order = a.order})

/-- C55 extends each prescribed within-sort order through the SAME
old map. Both the chosen source order and all its marked data persist. -/
theorem block_readout_reasonable (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (a : D.BlockReadoutOn priority A) :
    ∃ b : D.BlockReadoutOn priority B, D.restrictBlockReadout priority H e b = a := by
  obtain ⟨o,hfixed,ho⟩ := block_order_extension priority (D.supportStructure A).sort
    (D.supportStructure B).sort a.val.order a.property
      (D.supportEmbedding H e).point (D.supportEmbedding H e).injective (D.supportEmbedding H e).sort_eq
  refine ⟨⟨⟨o⟩,hfixed⟩,Subtype.ext ?_⟩
  apply ReadoutOn.ext
  apply LinearOrder.ext_lt
  exact ho

theorem block_readout_reasonable_lift (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (a : D.BlockReadoutOn priority A) :
    ∃ (b : D.BlockReadoutOn priority B) (f : D.ReadoutEmbedding H a.val b.val), f.old = e := by
  obtain ⟨b,hb⟩ := D.block_readout_reasonable priority H e a
  subst a
  exact ⟨b,D.restrictBlockReadoutEmbedding priority H e b,rfl⟩

end
end TupleInterpretation

end CCO.APRamseyReadout
