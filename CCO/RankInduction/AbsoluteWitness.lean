import CCO.RankInduction.Basis

/-! The final target is real algebraic closure under FULL original
automorphisms. Finite homogeneity proves the G-orbit implementation has
exactly that closure; a quotient full-group section is never asserted. -/

universe v w t
namespace CCO.RankInduction
open RawExact Owners.Product

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

abbrev AbsoluteWitness (safe : Set (S.Atom () ())) (A0 W : Set M) : Prop :=
  FiniteLift.OrdinaryWitness (G := G) (FiniteLift.aclSet (FiniteLift.FullAut G M))
    (S.menuRel safe) A0 W

include H in
theorem witness_absolute (safe : Set (S.Atom () ()))
    (A0 W : Set M) (finiteA : A0.Finite) (w : Witness S G safe A0 W) :
    AbsoluteWitness (G := G) S safe A0 W := by
  have hc := FiniteLift.aclSet_full_eq S H A0 finiteA
  refine ⟨w.finite,?_,w.extensions,?_⟩
  · rw [hc]
    exact w.closure
  · intro Z hZ z hz
    obtain ⟨α,hα,hz'⟩ := w.roots Z hZ z hz
    refine ⟨α,?_,hz'⟩
    intro x hx
    rw [hc]
    exact hα x hx

include H in
theorem closed_absolute (W : Set M) (finiteW : W.Finite)
    (closedW : FiniteLift.aclSet G W = W) :
    FiniteLift.aclSet (FiniteLift.FullAut G M) W = W :=
  (FiniteLift.aclSet_full_eq S H W finiteW).trans closedW

end CCO.RankInduction
