import CCO.ExactCRT.ExactLattice
import CCO.Owners.Product.SourceGeometry
import CCO.RawExact.CanonicalQuotientInheritance
import CCO.RealClosure.Bounds.SortRestriction

/-! Every actual exact quotient, including equality and top, is a genuine
one-sort standing source for the SAME original group. No finite-kernel or
properness assumption is involved. -/

universe v w t z
namespace CCO.Owners.Master

open RawExact ExactCRT CanonicalQuotients

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (E : ExactEq S H cco ())

local instance quotientInvariant : Invariant G E.val := Product.exactInvariant S H cco E

noncomputable def quotientData : ExactData S ({E.val} : Finset (Setoid A)) :=
  singletonData S E.val (exactPresentation S E.property)
    (exactPresentation_represents S E.property)

noncomputable def quotientSource : AtomicSource.{0,v,v} Unit (fun _ => Quotient E.val) := by
  letI : ∀ k : Index ({E.val} : Finset (Setoid A)), MulAction G (Carrier k) :=
    action S H (quotientData S H cco E)
  exact RealClosure.Bounds.sortSource (source S H (quotientData S H cco E))
    (singletonIndex E.val)

theorem quotientSource_homogeneous [Countable A] :
    HomogeneousSource (quotientSource S H cco E) G := by
  letI : ∀ k : Index ({E.val} : Finset (Setoid A)), MulAction G (Carrier k) :=
    action S H (quotientData S H cco E)
  exact RealClosure.Bounds.sortSource_homogeneous
    (source S H (quotientData S H cco E)) (singletonIndex E.val)
    (homogeneous S H cco (quotientData S H cco E))

theorem quotientSource_cco : SemanticCCO.{0,v,z,v} (quotientSource S H cco E) := by
  letI : ∀ k : Index ({E.val} : Finset (Setoid A)), MulAction G (Carrier k) :=
    action S H (quotientData S H cco E)
  exact RealClosure.Bounds.sortSource_semanticCCO
    (source S H (quotientData S H cco E)) (singletonIndex E.val)
    (semanticCCO S H cco (quotientData S H cco E))

theorem quotientSource_colour_orbital {i j : Unit}
    (x y x' y' : Quotient E.val) :
    (quotientSource S H cco E).colour (i := i) (j := j) x y =
      (quotientSource S H cco E).colour (i := i) (j := j) x' y' ↔
        GroupActions.orbital (G := G) x y x' y' := by
  cases i; cases j
  letI : ∀ k : Index ({E.val} : Finset (Setoid A)), MulAction G (Carrier k) :=
    action S H (quotientData S H cco E)
  exact source_colour_eq_iff_orbital S H (quotientData S H cco E)
    (k := singletonIndex E.val) (l := singletonIndex E.val) x y x' y'

theorem quotientSource_countable [Countable A] : Countable (Quotient E.val) :=
  (Quotient.mk''_surjective : Function.Surjective
    (Quotient.mk'' : A → Quotient E.val)).countable

end CCO.Owners.Master
