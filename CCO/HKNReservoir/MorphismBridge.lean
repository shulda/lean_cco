import CCO.HKNReservoir.HKNLanguage
import AllThoseEPPA.EPPA
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

universe u v w z x y
namespace CCO.HKNReservoir
open AllThoseEPPA
variable {B : Type u} {K : Type v} {Atom : Type w} {Γ : Type z} [Group Γ]
variable (tag : Γ →* Equiv.Perm B)
variable {V : Type x} {W : Type y}

/-- The exact CCO map data, with ONE retained global language component. -/
structure ExactMap (D : Data B K Atom V) (E : Data B K Atom W) where
  lang : Γ
  toFun : V → W
  injective : Function.Injective toFun
  owner : ∀ x, E.owner (toFun x) = tag lang (D.owner x)
  fine : ∀ a x y, E.fine a (toFun x) (toFun y) ↔ D.fine a x y
  move : ∀ k x, toFun (D.move k x) = E.move k (toFun x)

namespace ExactMap
variable {tag} {D : Data B K Atom V} {E : Data B K Atom W}

def toEmbedding (f : ExactMap tag D E) : Structure.Embedding (action tag) (encode D) (encode E) where
  lang := f.lang
  toFun := f.toFun
  injective := f.injective
  map_rel_iff := by
    intro n R xs
    cases R with
    | owner b =>
      change E.owner (f.toFun (xs 0)) = tag f.lang b ↔ D.owner (xs 0) = b
      rw [f.owner]
      exact (tag f.lang).injective.eq_iff
    | fine a => exact f.fine a (xs 0) (xs 1)
  map_func := by
    intro n F xs
    cases F with
    | translate k =>
      change f.toFun '' {D.move k (xs 0)} = {E.move k (f.toFun (xs 0))}
      rw [Set.image_singleton,f.move]
end ExactMap

/-- Exact external embeddings recover owner/fine reflection and equality
of the ENTIRE function-value sets, not merely a homomorphism inclusion. -/
def exactMapOfEmbedding {D : Data B K Atom V} {E : Data B K Atom W}
    (f : Structure.Embedding (action tag) (encode D) (encode E)) : ExactMap tag D E where
  lang := f.lang
  toFun := f.toFun
  injective := f.injective
  owner x := (f.map_rel_iff (.owner (D.owner x)) (fun _ => x)).mpr rfl
  fine a x y := by
    have h := f.map_rel_iff (.fine a) (![x,y])
    simpa only [encode_fine,action_fine,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.cons_val_fin_one] using h
  move k x := by
    have h := f.map_func (.translate k) (fun _ => x)
    change f.toFun '' {D.move k x} = {E.move k (f.toFun x)} at h
    rw [Set.image_singleton] at h
    exact Set.singleton_injective h

theorem embedding_iff_exactMap (D : Data B K Atom V) (E : Data B K Atom W) :
    Nonempty (Structure.Embedding (action tag) (encode D) (encode E)) ↔ Nonempty (ExactMap tag D E) :=
  ⟨fun ⟨f⟩ => ⟨exactMapOfEmbedding tag f⟩,fun ⟨f⟩ => ⟨f.toEmbedding⟩⟩

/-- Arbitrary HKN output structures are not assumed functional. The
embedding itself proves exact singleton values on the embedded source. -/
theorem embedding_function_value {D : Data B K Atom V} {E : Structure (Signature B K Atom) W}
    (f : Structure.Embedding (action tag) (encode D) E) (k : K) (x : V) :
    E.func (.translate k) (fun _ => f x) = {f (D.move k x)} := by
  have h := f.map_func (.translate k) (fun _ => x)
  change f.toFun '' {D.move k x} = E.func (.translate k) (fun _ => f x) at h
  simpa only [Set.image_singleton] using h.symm

theorem embedding_owner_iff {D : Data B K Atom V} {E : Structure (Signature B K Atom) W}
    (f : Structure.Embedding (action tag) (encode D) E) (b : B) (x : V) :
    E.rel (.owner (tag f.lang b)) (fun _ => f x) ↔ D.owner x = b :=
  f.map_rel_iff (.owner b) (fun _ => x)

theorem embedding_fine_iff {D : Data B K Atom V} {E : Structure (Signature B K Atom) W}
    (f : Structure.Embedding (action tag) (encode D) E) (a : Atom) (x y : V) :
    E.rel (.fine a) (![f x,f y]) ↔ D.fine a x y := by
  have h := f.map_rel_iff (.fine a) (![x,y])
  have he : f.toFun ∘ ![x,y] = ![f x,f y] := by funext i; fin_cases i <;> rfl
  rw [he] at h
  simpa only [encode_fine,action_fine,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.cons_val_fin_one,Function.comp_def] using h

structure ExactAut (D : Data B K Atom V) where
  lang : Γ
  perm : Equiv.Perm V
  owner : ∀ x, D.owner (perm x) = tag lang (D.owner x)
  fine : ∀ a x y, D.fine a (perm x) (perm y) ↔ D.fine a x y
  move : ∀ k x, perm (D.move k x) = D.move k (perm x)

namespace ExactAut
variable {tag} {D : Data B K Atom V}
def embedding (f : ExactAut tag D) : Structure.Embedding (action tag) (encode D) (encode D) :=
  (ExactMap.mk f.lang f.perm f.perm.injective f.owner f.fine f.move).toEmbedding

def toAutomorphism (f : ExactAut tag D) : Structure.Automorphism (action tag) (encode D) where
  toPartialIsomorphism := {
    lang := f.lang
    toPartialEquiv := f.perm.toPartialEquiv
    source_closed := Structure.isClosed_univ _
    target_closed := Structure.isClosed_univ _
    map_rel_iff := fun R xs _ => f.embedding.map_rel_iff R xs
    map_func := fun F xs _ => f.embedding.map_func F xs }
  source_eq_univ := rfl
  target_eq_univ := rfl
end ExactAut

end CCO.HKNReservoir
