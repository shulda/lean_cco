import CCO.FullPhaseLift.Canonical.FirstOrder
import Mathlib.Data.Bool.Basic

/-! Normalization is a proved change of symbol representation, not an
extra restriction on the finite relational source language. Total symbol
finiteness includes every arity and all nullary symbols. -/

universe u v w
namespace CCO.FullPhaseLift.Canonical
namespace Normalization
attribute [local instance] Classical.propDecidable
variable (L : R.Language.{u}) [Finite (Σ n, L.Rel n)]

@[instance_reducible] noncomputable def symbolFintype : Fintype (Σ n, L.Rel n) := Fintype.ofFinite _

noncomputable def code : (Σ n, L.Rel n) ≃ Fin (@Fintype.card _ (symbolFintype L)) :=
  @Fintype.equivFin _ (symbolFintype L)

noncomputable def signature : Signature where
  size := @Fintype.card _ (symbolFintype L)
  arity r := ((code L).symm r).1

@[simp] theorem arity_code (s : Σ n, L.Rel n) :
    (signature L).arity (code L s) = s.1 := by
  exact congrArg Sigma.fst ((code L).symm_apply_apply s)

noncomputable def table {V : Type v} (A : R.Structure L V) : BoolTable (signature L) V := by
  classical
  exact fun r xs => decide (A.rel ((code L).symm r).2 xs)

private theorem read_transport {V : Type v} (A : R.Structure L V)
    {s t : Σ n, L.Rel n} (h : s = t) (xs : Fin t.1 → V) :
    A.rel s.2 (xs ∘ Fin.cast (congrArg Sigma.fst h)) ↔ A.rel t.2 xs := by
  cases h
  simp only [Fin.cast_refl,Function.comp_id]

@[simp] theorem table_code {V : Type v} (A : R.Structure L V)
    (n : ℕ) (R : L.Rel n) (xs : Fin n → V) :
    table L A (code L ⟨n,R⟩) (xs ∘ Fin.cast (arity_code L ⟨n,R⟩)) =
      decide (A.rel R xs) := by
  classical
  apply Bool.decide_congr
  exact read_transport L A ((code L).symm_apply_apply ⟨n,R⟩) xs

noncomputable def embedding {V : Type v} {W : Type w}
    {A : R.Structure L V} {B : R.Structure L W}
    (e : RelationalCompletion.Relational.Structure.Embedding A B) :
    Embedding (table L A) (table L B) := by
  classical
  apply embeddingOf e.point e.injective
  intro r xs
  unfold table
  congr 1
  exact propext (e.rel_iff ((code L).symm r).2 xs)

noncomputable def forgetEmbedding {V : Type v} {W : Type w}
    {A : R.Structure L V} {B : R.Structure L W}
    (e : Embedding (table L A) (table L B)) :
    RelationalCompletion.Relational.Structure.Embedding A B where
  point := e.point
  injective := e.injective
  rel_iff R xs := by
    classical
    have h := embedding_read e (code L ⟨_,R⟩) (xs ∘ Fin.cast (arity_code L ⟨_,R⟩))
    have h' : decide (B.rel R (e.point ∘ xs)) = decide (A.rel R xs) := by
      simpa only [← Function.comp_assoc,table_code] using h
    simpa only [decide_eq_decide] using h'

noncomputable def iso {V : Type v} {W : Type w}
    {A : R.Structure L V} {B : R.Structure L W}
    (e : RelationalCompletion.Relational.Structure.Iso A B) :
    Iso (table L A) (table L B) := ⟨e.point,(embedding L e.toEmbedding).rel_iff⟩

noncomputable def forgetIso {V : Type v} {W : Type w}
    {A : R.Structure L V} {B : R.Structure L W}
    (e : Iso (table L A) (table L B)) :
    RelationalCompletion.Relational.Structure.Iso A B :=
  ⟨e.point,(forgetEmbedding L e.toEmbedding).rel_iff⟩

@[simp] theorem forget_embedding {V : Type v} {W : Type w}
    {A : R.Structure L V} {B : R.Structure L W}
    (e : RelationalCompletion.Relational.Structure.Embedding A B) :
    forgetEmbedding L (embedding L e) = e := by cases e; rfl

@[simp] theorem embedding_forget {V : Type v} {W : Type w}
    {A : R.Structure L V} {B : R.Structure L W}
    (e : Embedding (table L A) (table L B)) :
    embedding L (forgetEmbedding L e) = e := by cases e; rfl

@[simp] theorem forget_iso {V : Type v} {W : Type w}
    {A : R.Structure L V} {B : R.Structure L W}
    (e : RelationalCompletion.Relational.Structure.Iso A B) :
    forgetIso L (iso L e) = e := by cases e; rfl

@[simp] theorem iso_forget {V : Type v} {W : Type w}
    {A : R.Structure L V} {B : R.Structure L W}
    (e : Iso (table L A) (table L B)) :
    iso L (forgetIso L e) = e := by cases e; rfl

end Normalization
end CCO.FullPhaseLift.Canonical
