import CCO.RealHull.Geometry.ClassHomogeneity
import CCO.ParityHasse.Original.SourceHasse
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
# Actual finite class covers and the sharp old-atom exponent bound

The original FULL Hasse theorem is applied directly, without exactness of an
endpoint or class globalisation. A finite original interval chain multiplies
actual class counts by two. Every strict step adds an OLD diversity atom.
-/

universe u v w t
namespace CCO.RealHull.Geometry
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι)

def bottomClassEquiv (E : ColourEq S i) (a : X i) :
    RelativeClass (⊥ : ColourEq S i).val E.val a ≃ ClassPoint S i E a where
  toFun := Quotient.lift id (fun x y h => Subtype.ext h)
  invFun := Quotient.mk _
  left_inv q := by induction q using Quotient.inductionOn with | _ x => rfl
  right_inv _ := rfl

theorem class_subfinite (E F : ColourEq S i) (hFE : F ≤ E) (a : X i)
    [Finite (ClassPoint S i E a)] : Finite (ClassPoint S i F a) :=
  Finite.of_injective (fun x : ClassPoint S i F a =>
    (⟨x.val,hFE x.property⟩ : ClassPoint S i E a))
    (fun _ _ h => Subtype.ext (congrArg (fun z : ClassPoint S i E a => z.val) h))

theorem relative_finite_of_class (E F : ColourEq S i) (a : X i)
    [Finite (ClassPoint S i F a)] : Finite (RelativeClass E.val F.val a) := by
  unfold RelativeClass
  infer_instance

def classAtomMap (E F : ColourEq S i) (hFE : F ≤ E) (a : X i) :
    InducedAtom S i {x | F a x} ↪ InducedAtom S i {x | E a x} where
  toFun c := ⟨c.val,by
    obtain ⟨x,y,hc⟩ := c.property
    exact ⟨⟨x.val,hFE x.property⟩,⟨y.val,hFE y.property⟩,hc⟩⟩
  inj' _ _ h := Subtype.ext (congrArg
    (fun z : InducedAtom S i {x | E a x} => z.val) h)

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)
include H

theorem class_atom_card_strict (E F : ColourEq S i) (hFE : F < E) (a : X i) :
    Nat.card (InducedAtom S i {x | F a x}) < Nat.card (InducedAtom S i {x | E a x}) := by
  classical
  have hdiff : ∃ x y, E x y ∧ ¬ F x y := by
    by_contra hn
    apply hFE.not_ge
    intro x y hxy
    by_contra hF
    exact hn ⟨x,y,hxy,hF⟩
  obtain ⟨x,y,hE,hF⟩ := hdiff
  cases hc : S.colour x y with
  | none =>
    have he : x = y := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using (S.colour_none_iff x y).mp hc
    exact False.elim (hF (he ▸ F.val.refl x))
  | some c =>
    have he : ∀ u v, S.colour u v = some c → E u v := by
      intro u v huv
      exact (E.property x y u v (hc.trans huv.symm)).mp hE
    obtain ⟨p,q,hpq⟩ := (class_atom_occurs_iff S i H E a c).mpr he
    let d : InducedAtom S i {x | E a x} := ⟨c,p,q,hpq⟩
    have hns : ¬ Function.Surjective (classAtomMap S i E F hFE.le a) := by
      intro hs
      obtain ⟨b,hb⟩ := hs d
      have hval : b.val = c := congrArg Subtype.val hb
      have hf := (class_atom_occurs_iff S i H F a b.val).mp b.property
      exact hF (hf x y (hc.trans (congrArg some hval).symm))
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_lt_of_injective_not_surjective (classAtomMap S i E F hFE.le a)
        (classAtomMap S i E F hFE.le a).injective hns

theorem class_cover_index_two (cco : SemanticCCO.{u,v,0,w} S)
    (E F K : ColourEq S i) (hKE : K ≤ E) (hFK : F ⋖ K) (a : X i)
    [Finite (ClassPoint S i E a)] : relativeIndex F.val K.val a = 2 := by
  letI : Finite (ClassPoint S i K a) := class_subfinite S i E K hKE a
  letI : Finite (RelativeClass F.val K.val a) := relative_finite_of_class S i F K a
  exact full_relative_hasse S H cco F K hFK a

theorem finite_class_size_power_two (cco : SemanticCCO.{u,v,0,w} S)
    (E : ColourEq S i) (a : X i) [Finite (ClassPoint S i E a)] :
    ∃ n : Nat, Nat.card (ClassPoint S i E a) = 2^n ∧
      n ≤ Nat.card (InducedAtom S i {x | E a x}) := by
  classical
  suffices aux : ∀ F : ColourEq S i, Finite (ClassPoint S i F a) →
      ∃ n : Nat, Nat.card (ClassPoint S i F a) = 2^n ∧
        n ≤ Nat.card (InducedAtom S i {x | F a x}) by
    exact aux E inferInstance
  intro F
  induction F using WellFoundedLT.induction with
  | ind F ih =>
    intro hfin
    letI := hfin
    by_cases hF : F = ⊥
    · subst F
      letI : Subsingleton (ClassPoint S i (⊥ : ColourEq S i) a) := ⟨by
        intro x y
        apply Subtype.ext
        exact (show a = x.val from x.property).symm.trans y.property⟩
      have hc : Nat.card (ClassPoint S i (⊥ : ColourEq S i) a) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩
      exact ⟨0,by simpa only [pow_zero] using hc,Nat.zero_le _⟩
    · have hbot : (⊥ : ColourEq S i) < F := bot_lt_iff_ne_bot.mpr hF
      obtain ⟨Y,_,hYF⟩ := hbot.exists_le_covby
      letI : Finite (ClassPoint S i Y a) := class_subfinite S i F Y hYF.le a
      obtain ⟨n,hn,hbound⟩ := ih Y hYF.lt inferInstance
      letI : Finite (RelativeClass (⊥ : ColourEq S i).val F.val a) :=
        relative_finite_of_class S i ⊥ F a
      have hm := relativeIndex_mul S H (⊥ : ColourEq S i) Y F bot_le hYF.le a
      have htwo := class_cover_index_two S i H cco F Y F le_rfl hYF a
      have hcardF : relativeIndex (⊥ : ColourEq S i).val F.val a =
          Nat.card (ClassPoint S i F a) := Nat.card_congr (bottomClassEquiv S i F a)
      have hcardY : relativeIndex (⊥ : ColourEq S i).val Y.val a =
          Nat.card (ClassPoint S i Y a) := Nat.card_congr (bottomClassEquiv S i Y a)
      have hlt := class_atom_card_strict S i H F Y hYF.lt a
      refine ⟨n+1,?_,by omega⟩
      rw [← hcardF,hm,hcardY,hn,htwo,pow_succ]

omit H in theorem interval_cover_full (E : ColourEq S i) {F K : Set.Iic E} (hFK : F ⋖ K) :
    F.val ⋖ K.val := by
  refine ⟨hFK.lt,?_⟩
  intro Z hFZ hZK
  exact hFK.2 (show F < (⟨Z,le_trans hZK.le K.property⟩ : Set.Iic E) from hFZ) hZK

theorem finite_class_interval_cover_index_two (cco : SemanticCCO.{u,v,0,w} S)
    (E : ColourEq S i) (F K : Set.Iic E) (hFK : F ⋖ K) (a : X i)
    [Finite (ClassPoint S i E a)] : relativeIndex F.val.val K.val.val a = 2 :=
  class_cover_index_two S i H cco E F.val K.val K.property (interval_cover_full S i E hFK) a

/-- The finite SOURCE version can be instantiated on a genuine inherited
fibre before any globalisation. Finiteness of that actual carrier is explicit.
-/
theorem finite_sort_size_power_two (cco : SemanticCCO.{u,v,0,w} S) (a : X i)
    [Finite (X i)] :
    ∃ n : Nat, Nat.card (X i) = 2^n ∧ n ≤ Nat.card (S.Atom i i) := by
  classical
  letI : Finite (ClassPoint S i (⊤ : ColourEq S i) a) :=
    Finite.of_injective (fun x : ClassPoint S i (⊤ : ColourEq S i) a => x.val) Subtype.val_injective
  obtain ⟨n,hn,hbound⟩ := finite_class_size_power_two S i H cco ⊤ a
  let e : ClassPoint S i (⊤ : ColourEq S i) a ≃ X i := {
    toFun := Subtype.val
    invFun := fun x => ⟨x,trivial⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  refine ⟨n,(Nat.card_congr e).symm.trans hn,le_trans hbound ?_⟩
  letI := S.finiteAtom i i
  exact Nat.card_le_card_of_injective
    (fun c : InducedAtom S i {x | (⊤ : ColourEq S i) a x} => c.val) Subtype.val_injective

end CCO.RealHull.Geometry
