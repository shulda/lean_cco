import CCO.ExactEPGeometry.OriginalRetainedSelectedPresentedSeeds
import CCO.APCharacter.Masks

/-!
# B062 C88–C92: full-arrow character masks of ACTUAL selected quotient orbitals

The source C67 selected E-quotient CurrentSource is an ACTUAL homogeneous
finite-orbital source. Its genuinely full exact projected gates and FULL
Arrows were constructed in C82/C83. For any two such gates and a character
value assigned to each whole Arrow, this file defines the COMPLETE
orbital-local mask from real full Arrow relations, not from a chosen
generator or a nominal pair-colour table.

Actual pair homogeneity proves that legality of a REAL quotient orbital
is equivalent to the conditions read at ONE actual point pair. In
particular the whole projected gate identity (which need not be logical
equality of E-classes) forces duplicate gate-point prescriptions to agree.

The following generic lemmas are applied only to the actual C67 quotient
source and the C84 real selected-groupoid character in later consumers.
The required C88 identification with all original marked-age quotient
masks, and C89/C95 finite-age converse, are not assumed or claimed here.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The full character mask on one ACTUAL atomic colour, with the
complete pairwise rigid groupoid constraints. The old/quotient gate
identity is the WHOLE gate relation; it is not substituted by
logical point equality. -/
def originalSelectedCompleteAtomicMask
    (Q : CurrentSource.{u,v,w,t})
    {i j : Q.Sorts} (Kp : Kernel Q.source i)
    (Kq : Kernel Q.source j)
    (chi : Arrow Q.source Kp Kq → ZMod 2)
    (c : Option (Q.source.Atom i j))
    (eps eta : ZMod 2) : Prop :=
  ∀ (x : Q.Point i) (y : Q.Point j),
    Q.source.colour x y = c →
      ∀ (R : Arrow Q.source Kp Kq), R.rel x y →
        eta = eps + chi R

/-- Each actually OCCURRING selected quotient atomic orbital has
the same complete Arrow constraints at every real pair of its colour.
This is a consequence of actual Q homogeneity and exact-arrow
invariance; it holds for diagonal as well as diversity orbitals. -/
theorem originalSelectedCompleteAtomicMask_iff_at_pair
    (Q : CurrentSource.{u,v,w,t})
    {i j : Q.Sorts} (Kp : Kernel Q.source i)
    (Kq : Kernel Q.source j)
    (chi : Arrow Q.source Kp Kq → ZMod 2)
    (x : Q.Point i) (y : Q.Point j) (eps eta : ZMod 2) :
    originalSelectedCompleteAtomicMask Q Kp Kq chi
      (Q.source.colour x y) eps eta ↔
      ∀ (R : Arrow Q.source Kp Kq), R.rel x y →
        eta = eps + chi R := by
  constructor
  · intro h R hR
    exact h x y rfl R hR
  · intro h x' y' hc R hR'
    obtain ⟨g,hgx,hgy⟩ :=
      (Q.source.pair_homogeneous_of_homogeneous Q.homogeneous)
        x' x y' y hc
    have hR : R.rel x y := by
      simpa only [hgx,hgy] using
        R.exact.invariant Q.source Q.homogeneous g x' y' hR'
    exact h R hR

/-- If a full selected Arrow really contains the displayed
quotient pair, its literal atomic mask forces precisely THAT
Arrow character difference: another full Arrow containing the
same pair equals it by whole-Arrow freeness. -/
theorem originalSelectedCompleteAtomicMask_rigid_iff
    (Q : CurrentSource.{u,v,w,t})
    {i j : Q.Sorts} (Kp : Kernel Q.source i)
    (Kq : Kernel Q.source j)
    (chi : Arrow Q.source Kp Kq → ZMod 2)
    (x : Q.Point i) (y : Q.Point j)
    (R : Arrow Q.source Kp Kq) (hR : R.rel x y)
    (eps eta : ZMod 2) :
    originalSelectedCompleteAtomicMask Q Kp Kq chi
      (Q.source.colour x y) eps eta ↔
      eta = eps + chi R := by
  rw [originalSelectedCompleteAtomicMask_iff_at_pair]
  constructor
  · intro h
    exact h R hR
  · intro h T hT
    have hTR : T = R :=
      T.eq_of_common_real_pair Q.homogeneous R hT hR
    simpa only [hTR] using h

/-- An actual pair in no full gate Arrow is nonrigid:
both bit differences are admissible, with no hidden extra
orbit-choice equation. -/
theorem originalSelectedCompleteAtomicMask_nonrigid
    (Q : CurrentSource.{u,v,w,t})
    {i j : Q.Sorts} (Kp : Kernel Q.source i)
    (Kq : Kernel Q.source j)
    (chi : Arrow Q.source Kp Kq → ZMod 2)
    (x : Q.Point i) (y : Q.Point j)
    (hNonrigid : ∀ (R : Arrow Q.source Kp Kq), ¬ R.rel x y)
    (eps eta : ZMod 2) :
    originalSelectedCompleteAtomicMask Q Kp Kq chi
      (Q.source.colour x y) eps eta := by
  apply (originalSelectedCompleteAtomicMask_iff_at_pair
    Q Kp Kq chi x y eps eta).2
  intro R hR
  exact False.elim (hNonrigid R hR)

/-- Unlike quotient logical equality, the WHOLE selected K/E gate
identity relates different E-classes. On every genuine gate-related
pair, its zero character forces the same bit. -/
theorem originalSelectedCompleteAtomicMask_gate_iff
    (Q : CurrentSource.{u,v,w,t})
    {i : Q.Sorts} (K : Kernel Q.source i)
    (chi : Arrow Q.source K K → ZMod 2)
    (hId : chi (Arrow.id K) = 0)
    (x y : Q.Point i) (hK : K.rel x y)
    (eps eta : ZMod 2) :
    originalSelectedCompleteAtomicMask Q K K chi
      (Q.source.colour x y) eps eta ↔ eps = eta := by
  rw [originalSelectedCompleteAtomicMask_rigid_iff
    Q K K chi x y (Arrow.id K) hK eps eta, hId, add_zero]
  exact eq_comm

end
end CCO.ExactEPGeometry
