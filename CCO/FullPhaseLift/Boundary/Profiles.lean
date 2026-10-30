import CCO.FullPhaseLift.Boundary.Age
import CCO.FullPhaseLift.Canonical.Expansion
import CCO.FullPhaseLift.Full.Partial

/-! All unary and two-point old diagrams of an irreflexive 3-hypergraph
are empty, including every repeated-argument relation test. The canonical
expanded low diagram consequently depends only on real point equality. -/

universe u v
namespace CCO.FullPhaseLift.Boundary.HypergraphClass
open Canonical Full FreeAmalgam

theorem model_noRepeats : NoRepeats (relation modelTable) := by
  intro x y z h
  let xs := tuple3 x y z
  let V := Set.range xs
  letI : Finite V := (Set.finite_range xs).to_subtype
  let T := pullback modelTable (Subtype.val : V → Model)
  let e : Embedding T modelTable := embeddingOf Subtype.val Subtype.val_injective (fun _ _ => rfl)
  have ht := embedding_valid T e
  let a : V := ⟨x,⟨0,rfl⟩⟩
  let b : V := ⟨y,⟨1,rfl⟩⟩
  let c : V := ⟨z,⟨2,rfl⟩⟩
  have habc : relation T a b c := by
    change modelTable 0 (Subtype.val ∘ tuple3 a b c) = true
    rw [tuple3_comp]
    exact h
  obtain ⟨hab,hac,hbc⟩ := ht.1 a b c habc
  exact ⟨fun he => hab (Subtype.ext he),fun he => hac (Subtype.ext he),
    fun he => hbc (Subtype.ext he)⟩

theorem low_false {V : Type u} (T : BoolTable signature V) (hT : NoRepeats (relation T))
    (r : Fin signature.size) (xs : Fin (signature.arity r) → V) (hs : SmallSupport xs) :
    T r xs = false := by
  fin_cases r
  cases hb : T 0 xs with
  | false => exact hb
  | true =>
    have hR : relation T (xs 0) (xs 1) (xs 2) := by
      unfold relation
      rw [tuple3_eta]
      exact hb
    obtain ⟨h01,h02,h12⟩ := hT _ _ _ hR
    rcases hs 0 1 2 with he | he | he
    · exact (h01 he).elim
    · exact (h02 he).elim
    · exact (h12 he).elim

theorem profile_zero {V : Type u} (T : BoolTable signature V)
    (hT : NoRepeats (relation T)) (k : ℕ) (hk : k ≤ 2) (p : Fin k → V) :
    profile T p = fun _ => false := by
  funext a
  exact low_false T hT a.1 (p ∘ a.2) ((smallSupport_fin hk a.2).comp p)

theorem unary_zero {V : Type u} (T : BoolTable signature V)
    (hT : NoRepeats (relation T)) (x : V) : unaryProfile T x = fun _ => false :=
  profile_zero T hT 1 (by decide) _

theorem pair_zero {V : Type u} (T : BoolTable signature V)
    (hT : NoRepeats (relation T)) (x y : V) : pairProfile T x y = fun _ => false :=
  profile_zero T hT 2 (by decide) _

theorem sameSortSymmetric_of_noRepeats {V : Type u} (T : BoolTable signature V)
    (hT : NoRepeats (relation T)) : SameSortSymmetric T := by
  intro x y _
  rw [pair_zero T hT,pair_zero T hT]

theorem complete_noRepeats (V : Type u) : NoRepeats (relation (table (completeTriple V))) := by
  rw [relation_table]
  exact fun _ _ _ h => h

private theorem support_precomp {V : Type u} {k n : ℕ} {xs : Fin k → V}
    (hs : SmallSupport xs) (slots : Fin n → Fin k) : SmallSupport (xs ∘ slots) :=
  fun i j l => hs (slots i) (slots j) (slots l)

set_option maxRecDepth 8192 in
/-- Exact canonical FULL low truth transport. This uses all old tuples
and all the added qf names, preserving the irreflexive distinct-pair guard. -/
theorem expand_low {V : Type u} {W : Type v}
    (A : BoolTable signature V) (B : BoolTable signature W)
    (hA : NoRepeats (relation A)) (hB : NoRepeats (relation B)) (f : V ↪ W)
    (r : Fin (expansion signature).size)
    (xs : Fin ((expansion signature).arity r) → V) (hs : SmallSupport xs) :
    expand B r (f ∘ xs) = expand A r xs := by
  classical
  cases r using Fin.addCases with
  | left a =>
    have hc : signature.arity a = (expansion signature).arity (Fin.castAdd _ a) := by
      simp [expansion]
    have hs' : SmallSupport (xs ∘ Fin.cast hc) := support_precomp hs (Fin.cast hc)
    simpa only [expand,Fin.addCases_left,Function.comp_assoc] using
      (low_false B hB a _ (hs'.comp f)).trans (low_false A hA a _ hs').symm
  | right b =>
    cases b using Fin.addCases with
    | left a =>
      simp only [expand,Fin.addCases_right,Fin.addCases_left]
      rw [unary_zero B hB,unary_zero A hA]
    | right a =>
      simp only [expand,Fin.addCases_right]
      rw [pair_zero B hB,pair_zero A hA]
      exact decide_eq_decide.mpr (and_congr (not_congr f.injective.eq_iff) Iff.rfl)

end CCO.FullPhaseLift.Boundary.HypergraphClass
