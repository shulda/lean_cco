import CCO.UnaryFreshFrames.Age
import CCO.UnaryFreshFrames.ClosureActions
import Mathlib.Algebra.Group.Subgroup.Map

/-! The actual original real relational reduct. Its automorphism group is
FULL: every permutation preserving all original named sorts and relations.
No hidden homogeneity, orbit hypothesis or amalgamation is built into it. -/
universe u v
namespace CCO.PointGeneratedSAP
open UnaryFreshFrames

structure Original (L : Language.{u}) (V : Type v) (H : Structure L V) where
  realSort : L.Sorts → Prop
  originalRel : Set L.Rel

namespace Original
variable {L : Language.{u}} {V : Type v} {H : Structure L V} (O : Original L V H)
abbrev Real := {x : V // O.realSort (H.sort x)}

def automorphisms : Subgroup (Equiv.Perm O.Real) where
  carrier := {e | (∀ x, H.sort (e x).val = H.sort x.val) ∧
    ∀ R ∈ O.originalRel, ∀ xs : Fin (L.arity R) → O.Real,
      H.rel R (fun i => (e (xs i)).val) ↔ H.rel R (fun i => (xs i).val)}
  one_mem' := ⟨fun _ => rfl, fun _ _ _ => Iff.rfl⟩
  mul_mem' := by
    rintro e f ⟨heS,heR⟩ ⟨hfS,hfR⟩
    exact ⟨fun x => (heS (f x)).trans (hfS x),
      fun R hR xs => (heR R hR (f ∘ xs)).trans (hfR R hR xs)⟩
  inv_mem' := by
    rintro e ⟨heS,heR⟩
    refine ⟨?_,?_⟩
    · intro x
      exact (heS (e.symm x)).symm.trans (congrArg (fun z : O.Real => H.sort z.val) (e.apply_symm_apply x))
    · intro R hR xs
      have he := heR R hR (e.symm ∘ xs)
      have hh : (fun i => (e (e.symm (xs i))).val) = (fun i => (xs i).val) :=
        funext fun i => congrArg Subtype.val (e.apply_symm_apply (xs i))
      change (H.rel R (fun i => (e (e.symm (xs i))).val) ↔ _) at he
      rw [hh] at he
      exact he.symm

abbrev Aut := O.automorphisms

structure Embedding (D : Set O.Real) where
  point : D → O.Real
  injective : Function.Injective point
  sort_eq : ∀ x, H.sort (point x).val = H.sort x.val.val
  rel_iff : ∀ R ∈ O.originalRel, ∀ xs : Fin (L.arity R) → D,
    H.rel R (fun i => (point (xs i)).val) ↔ H.rel R (fun i => (xs i).val.val)

/-- Ordinary original real homogeneity, for ALL finite induced real maps. -/
def Homogeneous : Prop :=
  ∀ (D : Set O.Real), D.Finite → ∀ f g : O.Embedding D,
    ∃ a : O.Aut, ∀ x, a • f.point x = g.point x

end Original

/-- Structural data of an actual canonical equivariant unary interpretation.
The full original group acts on every relation and named unary map of H;
finite real closures and one-real-source term generation are explicit. -/
structure Interpretation {L : Language.{u}} {V : Type v} (H : Structure L V)
    (O : Original L V H) where
  lift : O.Aut →* H.Aut
  lift_real : ∀ g (x : O.Real), lift g • x.val = (g • x).val
  locallyFinite : ∀ D : Set O.Real, D.Finite → (H.closure (Subtype.val '' D)).Finite
  generating : ∀ x : V, ∃ r : O.Real, x ∈ H.closureAt r.val

end CCO.PointGeneratedSAP
