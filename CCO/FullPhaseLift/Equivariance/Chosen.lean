import CCO.FullPhaseLift.Full.ChosenPair

/-! B048 C25: the OPTIONAL automorphism-preserving source interface.
The chosen pair target is supplied as natural; no such target is inferred
from SAP. Applying the old interface to the augmented complete pair
diagram makes its own pair completion natural for its ENTIRE automorphism
group. The prescribed source permutations are then retained on the same
original vertex set. -/

universe v w
namespace CCO.FullPhaseLift.Equivariance
open Canonical Full

def PartialAuto {L : Signature} {V : Type v} (D : Partial L V)
    (e : Equiv.Perm V) : Prop :=
  ∀ r xs, D r (e ∘ xs) = D r xs

def PreservesFactors {L : Signature} {M : Type w} {V : Type v}
    {U : BoolTable L M} {D : Partial L V} {m : ℕ}
    (F : Fin m → FrozenFactor U D) (e : Equiv.Perm V) : Prop :=
  Set.range (fun j => Set.range (e ∘ (F j).inclusion)) =
    Set.range (fun j => Set.range (F j).inclusion)

def FullInvariant {L : Signature} {V : Type v} (T : BoolTable L V)
    (e : Equiv.Perm V) : Prop := ∀ r xs, T r (e ∘ xs) = T r xs

/-- Naturality here is exactly preservation of the chosen complete pair
diagram by every source automorphism preserving its frozen factor family. -/
def NaturalPair {L : Signature} {M : Type w} {V : Type v}
    (U : BoolTable L M) (D : Partial L V) {m : ℕ}
    (F : Fin m → FrozenFactor U D) (p : V → M) : Prop :=
  ∀ e : Equiv.Perm V, PartialAuto D e → PreservesFactors F e →
    LowEquivalent U (p ∘ e) p

/-- The source's OPTIONAL A04 form for a supplied natural strict pair
completion. The conclusion concerns one full completion preserving ALL
prescribed source automorphisms simultaneously. It is not an EPPA input
or a completion theorem derived from binary SAP. -/
def NaturalSupportNormal {L : Signature} {M : Type w} (U : BoolTable L M) : Prop :=
  ∀ (n : ℕ) (D : Partial L (Fin n)) (m : ℕ) (F : Fin m → FrozenFactor U D),
    Consistent U D → HigherCovered F →
    ∀ p : Fin n ↪ M, LowRealizes U D p → NaturalPair U D F p →
      ∃ f : Fin n → M, Realizes U D f ∧ (∀ j, (F j).FixedBy f) ∧
        ∀ e : Equiv.Perm (Fin n), PartialAuto D e → PreservesFactors F e →
          FullInvariant (pullback U f) e

private theorem smallSupport_of_comp {V : Type v} {W : Type w} {n : ℕ}
    (f : V → W) (hf : Function.Injective f) (xs : Fin n → V)
    (h : SmallSupport (f ∘ xs)) : SmallSupport xs := by
  intro i j k
  rcases h i j k with he | he | he
  · exact Or.inl (hf he)
  · exact Or.inr (Or.inl (hf he))
  · exact Or.inr (Or.inr (hf he))

/-- Once every low tuple is specified, its identity pair completion is
natural for ALL automorphisms of the augmented partial FULL diagram. -/
theorem augmented_natural {L : Signature} {M : Type w} {V : Type v}
    (U : BoolTable L M) (D : Partial L V) {m : ℕ}
    (F : Fin m → FrozenFactor U D) (p : V → M) (hp : LowRealizes U D p) :
    NaturalPair U (augmentLow U D p) (fun j => (F j).augment p hp) p := by
  intro e he _ r xs hs
  have hs' := hs.comp e
  have h := he r xs
  rw [augmentLow_small U D p r (e ∘ xs) hs',
    augmentLow_small U D p r xs hs] at h
  exact Option.some.inj h

theorem source_auto_augmented {L : Signature} {M : Type w} {V : Type v}
    (U : BoolTable L M) (D : Partial L V) (p : V → M)
    (e : Equiv.Perm V) (he : PartialAuto D e)
    (hn : LowEquivalent U (p ∘ e) p) : PartialAuto (augmentLow U D p) e := by
  intro r xs
  by_cases hs : SmallSupport xs
  · rw [augmentLow_small U D p r (e ∘ xs) (hs.comp e),
      augmentLow_small U D p r xs hs]
    exact congrArg some (hn r xs hs)
  · have hs' : ¬SmallSupport (e ∘ xs) :=
      fun h => hs (smallSupport_of_comp e e.injective xs h)
    rw [augmentLow_high U D p r (e ∘ xs) hs',augmentLow_high U D p r xs hs]
    exact he r xs

/-- The source group may preserve extra unary bits. No naturality for the
larger automorphism group of the FORGOTTEN old partial diagram is assumed.
The old A04 is instead used on the augmented diagram, whose own completed
pair diagram is automatically natural for its whole automorphism group. -/
theorem chosen_lift {L : Signature} {M : Type w}
    (U : BoolTable L M) (sep : SeparatesPoints U) (equivariant : NaturalSupportNormal U)
    (n : ℕ) (D : Partial L (Fin n)) (m : ℕ) (F : Fin m → FrozenFactor U D)
    (covered : HigherCovered F) (p : Fin n ↪ M) (hp : LowRealizes U D p)
    (Γ : Set (Equiv.Perm (Fin n)))
    (hΓ : ∀ e ∈ Γ, PartialAuto D e ∧ PreservesFactors F e ∧ LowEquivalent U (p ∘ e) p) :
    ∃ q : Fin n ↪ M, Realizes U D q ∧ (∀ j, (F j).FixedBy q) ∧
      LowEquivalent U q p ∧ ∀ e ∈ Γ, FullInvariant (pullback U q) e := by
  let D' := augmentLow U D p
  let F' : Fin m → FrozenFactor U D' := fun j => (F j).augment p hp
  have hpair : LowRealizes U D' p := by
    intro r xs b hs hd
    change augmentLow U D p r xs = some b at hd
    rw [augmentLow_small U D p r xs hs] at hd
    exact Option.some.inj hd
  obtain ⟨q,hq,hfix,hauto⟩ := equivariant n D' m F'
    (augmentLow_consistent U D p) (higherCovered_augment F covered p hp)
    p hpair (augmented_natural U D F p hp)
  have hl : LowEquivalent U q p := by
    intro r xs hs
    exact hq r xs _ (augmentLow_small U D p r xs hs)
  let q' : Fin n ↪ M := ⟨q,injective_of_lowEquivalent U sep p q hl⟩
  refine ⟨q',?_,hfix,hl,?_⟩
  · intro r xs b hd
    exact hq r xs b (augmentLow_extends U D p hp r xs b hd)
  · intro e he
    obtain ⟨hD,hF,hn⟩ := hΓ e he
    exact hauto e (source_auto_augmented U D p e hD hn) hF

end CCO.FullPhaseLift.Equivariance
