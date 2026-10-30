import CCO.FullPhaseLift.Tower.Reduct
import CCO.FullPhaseLift.Marked.Class
import CCO.FullPhaseLift.BinarySource.FullAlignment

/-! A genuine global FULL reduct supplies the finite-age forgetful
functor on the SAME point maps. Old full homogeneity proves exact-map
reasonableness; finite languages prove finite expansion fibres. -/
universe m n
namespace CCO.FullPhaseLift.Tower.FullReduct
open Canonical Marked APCharacter CategoryTheory
noncomputable section
variable {L K : Signature} {M : Type m} {N : Type n}
variable {U : BoolTable L M} {V : BoolTable K N} (P : FullReduct U V)

/-- Forget old-symbol coordinates in a full embedding without changing
its vertex map. -/
def signatureEmbedding {A : Type} {B : Type}
    {TA : BoolTable K A} {TB : BoolTable K B} (f : Canonical.Embedding TA TB) :
    Canonical.Embedding (P.signature.forget TA) (P.signature.forget TB) :=
  embeddingOf f.point f.injective
    (fun r xs => embedding_read f (P.signature.symbol r) (xs ∘ Fin.cast (P.signature.arity r)))

/-- The actual global old FULL isomorphism carries each finite full
substructure to a genuine old age object. -/
def projectEmbedding (C : OldChart V) :
    Canonical.Embedding (P.signature.forget C.full) U := by
  let c := C.realized.some
  apply embeddingOf (P.point ∘ c.point) (P.point.injective.comp c.injective)
  intro r xs
  exact ((P.tuple_read r (c.point ∘ xs)).symm).trans
    (embedding_read c (P.signature.symbol r) (xs ∘ Fin.cast (P.signature.arity r)))

def object (C : OldChart V) : OldChart U :=
  ⟨C.size,P.signature.forget C.full,⟨P.projectEmbedding C⟩⟩

def forget : OldChart V ⥤ OldChart U where
  obj := P.object
  map f := P.signatureEmbedding f
  map_id := by intros; rfl
  map_comp := by intros; rfl

private theorem oldChart_ext {A B : OldChart U} (hs : A.size = B.size)
    (ht : HEq A.full B.full) : A = B := by
  cases A
  cases B
  cases hs
  cases eq_of_heq ht
  rfl

private theorem embedding_heq {A : Type} {B : Type}
    {TA : BoolTable L A} {TB TC : BoolTable L B} (ht : TB = TC)
    (f : Canonical.Embedding TA TB) (g : Canonical.Embedding TA TC)
    (hp : ∀ x, f.point x = g.point x) : HEq f g := by
  cases ht
  apply heq_of_eq
  cases f
  cases g
  have h := funext hp
  cases h
  rfl

/-- Finite full tables on one fixed finite carrier form a finite set. -/
theorem finite_size (k : ℕ) : Finite {C : OldChart V // C.size = k} := by
  let target := Σ i : {j : ℕ // j = k}, BoolTable K (Fin i.val)
  let code : {C : OldChart V // C.size = k} → target :=
    fun C => ⟨⟨C.val.size,C.property⟩,C.val.full⟩
  apply Finite.of_injective code
  rintro ⟨⟨a,TA,hA⟩,ha⟩ ⟨⟨b,TB,hB⟩,hb⟩ he
  cases he
  rfl

theorem precompact : Towers.Precompact P.forget := by
  intro B
  letI := finite_size (V := V) B.size
  let code : {C : OldChart V // P.forget.obj C = B} → {C : OldChart V // C.size = B.size} :=
    fun C => ⟨C.val,congrArg OldChart.size C.property⟩
  apply Finite.of_injective code
  intro A C he
  exact Subtype.ext (congrArg (fun C : {C : OldChart V // C.size = B.size} => C.val) he)

/-- A full old object lifts along the ACTUAL global reduct bijection,
with exactly its original finite carrier and every old tuple unchanged. -/
theorem reductSurjective : Towers.ReductSurjective P.forget := by
  intro B
  let b := B.realized.some
  let q : Fin B.size ↪ N := ⟨P.point.symm ∘ b.point,P.point.symm.injective.comp b.injective⟩
  let C : OldChart V :=
    ⟨B.size,pullback V q,⟨embeddingOf q q.injective (fun _ _ => rfl)⟩⟩
  refine ⟨C,?_⟩
  apply oldChart_ext (A := P.object C) (B := B) rfl
  apply heq_of_eq
  funext r xs
  change V (P.signature.symbol r) (q ∘ (xs ∘ Fin.cast (P.signature.arity r))) = B.full r xs
  have hr := P.tuple_read r (q ∘ xs)
  have he : (P.point : N → M) ∘ (q ∘ xs) = b.point ∘ xs := by
    funext i
    exact P.point.apply_symm_apply _
  exact hr.trans ((congrArg (U r) he).trans (embedding_read b r xs))

/-- Old FULL homogeneity aligns the prescribed base map. The lifted
embedding is the SAME map, and all target old relations remain fixed. -/
theorem reasonable (hom : (toRelational U).Homogeneous) : Towers.Reasonable P.forget := by
  intro C B f
  let c := C.realized.some
  let b := B.realized.some
  let pc := P.projectEmbedding C
  let qb := b.comp f
  obtain ⟨a,ha⟩ := BinarySource.full_tuple_homogeneous (toRelational U) hom pc.point qb.point
    (fun x y => pc.injective.eq_iff.trans qb.injective.eq_iff.symm)
    (fun R xs => (pc.rel_iff R xs).trans (qb.rel_iff R xs).symm)
  let q : Fin B.size ↪ N :=
    ⟨fun x => P.point.symm (a.point.symm (b.point x)),
      P.point.symm.injective.comp (a.point.symm.injective.comp b.injective)⟩
  have hq (x : Fin C.size) : q (f.point x) = c.point x := by
    apply P.point.injective
    change P.point (P.point.symm (a.point.symm (b.point (f.point x)))) = P.point (c.point x)
    rw [P.point.apply_symm_apply]
    have h := ha x
    change a.point (P.point (c.point x)) = b.point (f.point x) at h
    rw [← h,a.point.symm_apply_apply]
  let D : OldChart V :=
    ⟨B.size,pullback V q,⟨embeddingOf q q.injective (fun _ _ => rfl)⟩⟩
  have hT : P.signature.forget D.full = B.full := by
    funext r xs
    have hr := P.tuple_read r (q ∘ xs)
    have he : (P.point : N → M) ∘ (q ∘ xs) = a.point.symm ∘ (b.point ∘ xs) := by
      funext i
      exact P.point.apply_symm_apply _
    exact hr.trans ((congrArg (U r) he).trans
      ((embedding_read a.symm.toEmbedding r (b.point ∘ xs)).trans (embedding_read b r xs)))
  have hd : P.object D = B := oldChart_ext (A := P.object D) (B := B) rfl (heq_of_eq hT)
  let g : C ⟶ D := embeddingOf f.point f.injective (by
    intro r xs
    change V r (q ∘ (f.point ∘ xs)) = C.full r xs
    have he : (q : Fin B.size → N) ∘ (f.point ∘ xs) = c.point ∘ xs :=
      funext (fun i => hq (xs i))
    exact (congrArg (V r) he).trans (embedding_read c r xs))
  refine ⟨D,g,hd,?_⟩
  exact embedding_heq hT (P.signatureEmbedding g) f (fun _ => rfl)

/-- All three properties belong to this literal full-relation reduct
functor, independently of any binary comparison isomorphism. -/
def transition (hom : (toRelational U).Homogeneous) :
    Towers.UnaryTransition ⟨OldChart U,oldCategory U⟩ ⟨OldChart V,oldCategory V⟩ where
  forget := P.forget
  reasonable := P.reasonable hom
  reductSurjective := P.reductSurjective
  precompact := P.precompact

end
end CCO.FullPhaseLift.Tower.FullReduct
