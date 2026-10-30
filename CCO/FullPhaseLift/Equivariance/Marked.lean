import CCO.FullPhaseLift.Equivariance.Chosen
import CCO.FullPhaseLift.Marked.Signature

/-! Restore the prescribed unary bits on the SAME full chosen completion.
Every supplied source permutation acts by its original permutation of the
original finite vertices and preserves all old higher-arity relations. -/

universe v w
namespace CCO.FullPhaseLift.Equivariance
open Canonical Full

theorem restore_bits_invariant {L : Signature} {V : Type v}
    (T : BoolTable L V) (bits : V → APCharacter.Bit) (e : Equiv.Perm V)
    (hT : FullInvariant T e) (hb : ∀ x, bits (e x) = bits x) :
    FullInvariant (Marked.table T bits) e := by
  intro r
  refine Fin.cases ?_ (fun s => ?_) r
  · intro xs
    change Marked.bitBool (bits (e (xs (0 : Fin 1)))) =
      Marked.bitBool (bits (xs (0 : Fin 1)))
    rw [hb]
  · intro xs
    exact hT s xs

/-- An actual full expanded automorphism, retaining the exact source
permutation rather than choosing another automorphism on the same bits. -/
def restoredIso {L : Signature} {V : Type v}
    (T : BoolTable L V) (bits : V → APCharacter.Bit) (e : Equiv.Perm V)
    (hT : FullInvariant T e) (hb : ∀ x, bits (e x) = bits x) :
    Iso (Marked.table T bits) (Marked.table T bits) :=
  isoOf e (restore_bits_invariant T bits e hT hb)

theorem restoredIso_point {L : Signature} {V : Type v}
    (T : BoolTable L V) (bits : V → APCharacter.Bit) (e : Equiv.Perm V)
    (hT : FullInvariant T e) (hb : ∀ x, bits (e x) = bits x) :
    (restoredIso T bits e hT hb).point = e := rfl

/-- C25's finite target: the OPTIONAL old A04 supplies one full lift,
and a supplied natural marked pair target supplies its fixed bits. All
prescribed original automorphisms are simultaneously automorphisms of
this SAME full marked object. Its old object is actually embedded in U. -/
theorem chosen_marked_target {L : Signature} {M : Type w}
    (U : BoolTable L M) (sep : SeparatesPoints U) (equivariant : NaturalSupportNormal U)
    (n : ℕ) (D : Partial L (Fin n)) (m : ℕ) (F : Fin m → FrozenFactor U D)
    (covered : HigherCovered F) (p : Fin n ↪ M) (hp : LowRealizes U D p)
    (bits : Fin n → APCharacter.Bit) (Γ : Set (Equiv.Perm (Fin n)))
    (hΓ : ∀ e ∈ Γ, PartialAuto D e ∧ PreservesFactors F e ∧ LowEquivalent U (p ∘ e) p)
    (hbits : ∀ e ∈ Γ, ∀ x, bits (e x) = bits x) :
    ∃ q : Fin n ↪ M, Realizes U D q ∧ (∀ j, (F j).FixedBy q) ∧
      LowEquivalent U q p ∧ Nonempty (Embedding (pullback U q) U) ∧
      ∀ e ∈ Γ, ∃ a : Iso (Marked.table (pullback U q) bits)
          (Marked.table (pullback U q) bits), a.point = e := by
  obtain ⟨q,hq,hF,hl,ha⟩ := chosen_lift U sep equivariant n D m F covered p hp Γ hΓ
  refine ⟨q,hq,hF,hl,⟨embeddingOf q q.injective (fun _ _ => rfl)⟩,?_⟩
  intro e he
  exact ⟨restoredIso (pullback U q) bits e (ha e he) (hbits e he),rfl⟩

end CCO.FullPhaseLift.Equivariance
