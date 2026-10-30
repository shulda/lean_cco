import CCO.FullPhaseLift.Canonical.FirstOrder
import CCO.OwnerTransversal.PacketBackAndForth
import Mathlib.Data.Fintype.EquivFin

/-! Countable back-and-forth retaining the ENTIRE old relational table.
The finite extension hypotheses must be proved from actual full ages and
reasonableness. No binary isomorphism is used for higher tuples. -/

open scoped FirstOrder
open FirstOrder FirstOrder.Language
universe u v
namespace CCO.FullPhaseLift.BinarySource
open Canonical
noncomputable section

def FullFiniteExtension {L : Signature} {M : Type u} {N : Type v}
    (U : BoolTable L M) (V : BoolTable L N) : Prop :=
  ∀ (n m : ℕ) (j : Fin n ↪ Fin m) (p : Fin m ↪ M) (q : Fin n ↪ N),
    (∀ r xs, V r (q ∘ xs) = U r ((p ∘ j) ∘ xs)) →
    ∃ f : Fin m ↪ N, (∀ r xs, V r (f ∘ xs) = U r (p ∘ xs)) ∧
      ∀ x, f (j x) = q x

theorem fullFiniteExtension_firstOrder {L : Signature} {M : Type u} {N : Type v}
    (U : BoolTable L M) (V : BoolTable L N) (ext : FullFiniteExtension U V) :
    letI := toFirstOrder U
    letI := toFirstOrder V
    OwnerTransversal.PacketBackAndForth.FiniteExtension L.firstOrder M N := by
  classical
  letI := toFirstOrder U
  letI := toFirstOrder V
  intro A B _ _ hAB f
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  let a := Fintype.equivFin A
  let b := Fintype.equivFin B
  let inc : A ↪ B := ⟨fun x => ⟨x.val,hAB x.property⟩,by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun x : B => x.val) he⟩
  let j := a.symm.toEmbedding.trans (inc.trans b.toEmbedding)
  let p := b.symm.toEmbedding.trans B.subtype.toEmbedding
  let q := a.symm.toEmbedding.trans f.toEmbedding
  have hp (x : Fin (Fintype.card A)) : p (j x) = (a.symm x).val := by
    change (b.symm (b (inc (a.symm x)))).val = (a.symm x).val
    rw [b.symm_apply_apply]
    rfl
  have hf (r : Fin L.size) (xs : Fin (L.arity r) → A) :
      V r ((f : A → N) ∘ xs) = U r (Subtype.val ∘ xs) := by
    have h := f.map_rel (⟨r,rfl⟩ : L.firstOrder.Relations (L.arity r)) xs
    change (V r ((f : A → N) ∘ xs) = true ↔ U r (Subtype.val ∘ xs) = true) at h
    exact Bool.eq_iff_iff.mpr h
  obtain ⟨g,hg,he⟩ := ext _ _ j p q (by
    intro r xs
    have hh := hf r (a.symm ∘ xs)
    have htuple : (p ∘ j) ∘ xs = Subtype.val ∘ (a.symm ∘ xs) :=
      funext (fun i => hp (xs i))
    rw [htuple]
    exact hh)
  let k : B ↪ N := b.toEmbedding.trans g
  have hk (r : Fin L.size) (xs : Fin (L.arity r) → B) :
      V r (k ∘ xs) = U r (Subtype.val ∘ xs) := by
    have h := hg r (b ∘ xs)
    have ht : p ∘ (b ∘ xs) = Subtype.val ∘ xs := by
      funext i
      change (b.symm (b (xs i))).val = (xs i).val
      rw [b.symm_apply_apply]
    rw [ht] at h
    exact h
  let g' : B ↪[L.firstOrder] N := {
    toFun := k
    inj' := k.injective
    map_fun' F := nomatch F
    map_rel' := by
      intro n R xs
      rcases R with ⟨r,hr⟩
      subst n
      change (V r (k ∘ xs) = true) ↔ U r (Subtype.val ∘ xs) = true
      rw [hk] }
  refine ⟨g',?_⟩
  ext x
  have hx := he (a x)
  have hj : j (a x) = b (inc x) := by
    change b (inc (a.symm (a x))) = b (inc x)
    rw [a.symm_apply_apply]
  rw [hj] at hx
  change g (b (inc x)) = f (a.symm (a x)) at hx
  change g (b (inc x)) = f x
  simpa only [a.symm_apply_apply] using hx

/-- Starting with the actual common empty diagram retains its nullary
truths. Finite and empty full structures therefore work as well. -/
theorem fullIso_of_finiteExtension {L : Signature} {M : Type u} {N : Type v}
    [Countable M] [Countable N] (U : BoolTable L M) (V : BoolTable L N)
    (forth : FullFiniteExtension U V) (back : FullFiniteExtension V U)
    (empty : ∀ r (xs : Fin (L.arity r) → Fin 0),
      V r (Fin.elim0 ∘ xs) = U r (Fin.elim0 ∘ xs)) :
    Nonempty (Canonical.Iso U V) := by
  classical
  letI := toFirstOrder U
  letI := toFirstOrder V
  let A : L.firstOrder.Substructure M := {
    carrier := ∅
    fun_mem := by intro n f; exact Empty.elim f }
  letI : Finite A := Set.finite_empty.to_subtype
  let f : A ↪[L.firstOrder] N := {
    toFun a := a.property.elim
    inj' := by intro a; exact a.property.elim
    map_fun' F := nomatch F
    map_rel' := by
      intro n R xs
      rcases R with ⟨r,hr⟩
      subst n
      let slots : Fin (L.arity r) → Fin 0 := fun i => (xs i).property.elim
      have heN : (fun a : A => (a.property.elim : N)) ∘ xs = Fin.elim0 ∘ slots := by
        funext i
        exact (xs i).property.elim
      have heM : Subtype.val ∘ xs = (Fin.elim0 : Fin 0 → M) ∘ slots := by
        funext i
        exact (xs i).property.elim
      change (V r ((fun a : A => (a.property.elim : N)) ∘ xs) = true) ↔
        U r (Subtype.val ∘ xs) = true
      rw [heN,heM,empty] }
  have finiteM : OwnerTransversal.PacketBackAndForth.LocallyFinite L.firstOrder M := by
    intro A hA
    exact hA.finite
  have finiteN : OwnerTransversal.PacketBackAndForth.LocallyFinite L.firstOrder N := by
    intro A hA
    exact hA.finite
  obtain ⟨e,_⟩ := OwnerTransversal.PacketBackAndForth.equiv_extending L.firstOrder M N
    finiteM finiteN (fullFiniteExtension_firstOrder U V forth)
    (fullFiniteExtension_firstOrder V U back) A f
  exact ⟨isoOfFirstOrder e⟩

end
end CCO.FullPhaseLift.BinarySource
