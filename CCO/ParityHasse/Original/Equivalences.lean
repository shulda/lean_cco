import CCO.Supports
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Atoms.Finite
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The full original colour-invariant equivalence poset

Every `Setoid` constant on actual optional pair colours is admitted. There
is no exactness, definability expansion, SAP, or CCO premise in these
definitions. Relative classes are actual quotient classes inside one
containing equivalence class; their cardinal is `Nat.card`, so finiteness
must be supplied when a positive finite index is used.
-/

universe u v w

namespace CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}

/-- Constancy on the full actual named colour, including real equality. -/
def ColourInvariant (S : AtomicSource ι X) (i : ι)
    (R : X i → X i → Prop) : Prop :=
  ∀ x y x' y', S.colour x y = S.colour x' y' → (R x y ↔ R x' y')

/-- ALL original colour-invariant equivalences, rather than an exact menu. -/
abbrev ColourEq (S : AtomicSource ι X) (i : ι) :=
  { E : Setoid (X i) // ColourInvariant S i E }

namespace ColourEq

variable (S : AtomicSource ι X) (i : ι)

instance : PartialOrder (ColourEq S i) := inferInstanceAs (PartialOrder { E : Setoid (X i) // _ })

instance : CoeFun (ColourEq S i) (fun _ => X i → X i → Prop) :=
  ⟨fun E => E.val.r⟩

@[ext] theorem ext {E F : ColourEq S i}
    (h : ∀ x y, E x y ↔ F x y) : E = F :=
  Subtype.ext (Setoid.ext h)

instance : OrderTop (ColourEq S i) where
  top := ⟨⊤, fun _ _ _ _ _ => Iff.rfl⟩
  le_top := fun _ _ _ _ => trivial

instance : OrderBot (ColourEq S i) where
  bot := ⟨⊥, by
    intro x y x' y' hcol
    have hn : S.colour x y = none ↔ S.colour x' y' = none := by rw [hcol]
    change x = y ↔ x' = y'
    simpa only [S.colour_none_iff, Sigma.mk.injEq, heq_eq_eq, true_and] using hn⟩
  bot_le := fun E x y hxy => hxy ▸ E.val.refl x

instance : SemilatticeInf (ColourEq S i) where
  inf E F := ⟨E.val ⊓ F.val, fun x y x' y' hc => and_congr (E.2 _ _ _ _ hc) (F.2 _ _ _ _ hc)⟩
  inf_le_left := fun _ _ _ _ h => h.1
  inf_le_right := fun _ _ _ _ h => h.2
  le_inf := fun _ _ _ hE hF _ _ h => ⟨hE h, hF h⟩

@[simp] theorem top_apply (x y : X i) : (⊤ : ColourEq S i) x y ↔ True := Iff.rfl
@[simp] theorem bot_apply (x y : X i) : (⊥ : ColourEq S i) x y ↔ x = y := Iff.rfl
@[simp] theorem inf_apply (E F : ColourEq S i) (x y : X i) :
    (E ⊓ F) x y ↔ E x y ∧ F x y := Iff.rfl

/-- The finite actual optional palette separates the full equivalence poset. -/
theorem support_injective : Function.Injective
    (fun E : ColourEq S i => S.rawSupport (i := i) (j := i) E) := by
  intro E F h
  change S.rawSupport (fun x y => E x y) = S.rawSupport (fun x y => F x y) at h
  apply ext
  intro x y
  constructor
  · intro hxy
    have hc : S.colour x y ∈ S.rawSupport F := by
      rw [← h]
      exact ⟨x, y, hxy, rfl⟩
    obtain ⟨a, b, hab, hcol⟩ := hc
    exact (F.2 a b x y hcol).mp hab
  · intro hxy
    have hc : S.colour x y ∈ S.rawSupport E := by
      rw [h]
      exact ⟨x, y, hxy, rfl⟩
    obtain ⟨a, b, hab, hcol⟩ := hc
    exact (E.2 a b x y hcol).mp hab

instance : Finite (ColourEq S i) := by
  letI := S.finiteAtom i i
  exact Finite.of_injective _ (support_injective S i)

/-- Consequently every interval is finite, even before a finite-index premise. -/
theorem finite_interval (E F : ColourEq S i) : (Set.Icc E F).Finite := Set.toFinite _

/-- A proper equivalence lies below a full-poset last cover of Top. -/
theorem exists_last_cover {E : ColourEq S i} (hE : E < ⊤) :
    ∃ F : ColourEq S i, E ≤ F ∧ F ⋖ ⊤ := hE.exists_le_covby

end ColourEq

/-- Actual E-classes inside the F-class of a, without endpoint exactness. -/
def RelativeClass {A : Type v} (E F : Setoid A) (a : A) : Type v :=
  Quotient (Setoid.comap (fun x : {x // F a x} => x.val) E)

/-- The number of actual relative classes; finite-index uses additionally
require `Finite (RelativeClass E F a)`, rather than interpreting zero as infinity. -/
noncomputable def relativeIndex {A : Type v} (E F : Setoid A) (a : A) : Nat :=
  Nat.card (RelativeClass E F a)

/-- Relative classes inject into all E-classes. Thus finite global index
makes every relative class set finite, independently of uniformity. -/
def relativeClassToQuotient {A : Type v} (E F : Setoid A) (a : A) :
    RelativeClass E F a → Quotient E :=
  Quotient.map Subtype.val (fun _ _ h => h)

theorem relativeClassToQuotient_injective {A : Type v} (E F : Setoid A) (a : A) :
    Function.Injective (relativeClassToQuotient E F a) := by
  intro q r h
  induction q using Quotient.inductionOn with | _ x =>
    induction r using Quotient.inductionOn with | _ y =>
      change Quotient.mk E x.val = Quotient.mk E y.val at h
      apply Quotient.sound
      exact (Quotient.exact h : E x.val y.val)

instance finite_relativeClass_of_finite_global {A : Type v}
    (E F : Setoid A) (a : A) [Finite (Quotient E)] :
    Finite (RelativeClass E F a) :=
  Finite.of_injective _ (relativeClassToQuotient_injective E F a)

/-- At Top the relative quotient is precisely the global quotient. -/
def topRelativeClassEquiv {A : Type v} (E : Setoid A) (a : A) :
    RelativeClass E ⊤ a ≃ Quotient E where
  toFun := relativeClassToQuotient E ⊤ a
  invFun := Quotient.map (fun x => (⟨x, trivial⟩ : {x // (⊤ : Setoid A) a x}))
    (fun _ _ h => h)
  left_inv q := by induction q using Quotient.inductionOn; rfl
  right_inv q := by induction q using Quotient.inductionOn; rfl

@[simp] theorem relativeIndex_top {A : Type v} (E : Setoid A) (a : A) :
    relativeIndex E ⊤ a = Nat.card (Quotient E) :=
  Nat.card_congr (topRelativeClassEquiv E a)

end CCO.ParityHasse.Original
