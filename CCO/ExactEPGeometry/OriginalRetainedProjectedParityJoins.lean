import CCO.ExactEPGeometry.OriginalRetainedQuotientParityProfiles
import CCO.ParityHasse.Original.OrbitalAlgebra

/-!
# B062 C98 / source E11: actual invariant-equivalence joins in quotient parity

For genuine original colour-invariant equivalences e and Y, symmetric
homogeneity makes their relational composition the full setoid join.
Consequently E-bisaturation e;Y;e is LITERALLY e join Y; the same holds
for the original connectivity equivalence X. The original odd profile O
is not a setoid and remains its true two-sided E-saturation e;O;e.

We instantiate these identities on the SAME old source phase-odd pivot
and its TRUE nonempty all-parent E-quotient diversity orbital, using the
previously compiled complete even/odd/connected quotient profile
pullbacks. All zero-length identities and all original E-classes remain
literal; no quotient SAP, arbitrary reverse exact descent, group section,
or new source assumption is introduced.

This settles the relation identities underlying E11 on the actual
all-parent quotient. Selected occupancy retyping, the largest original
quotient gate lift and the full marked age are separate tasks.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- In the genuine symmetric homogeneous original source, E;F;E
equals the full setoid join E sup F for actual invariant equivalences.
Both endpoint E edges are retained, including true old equality. -/
theorem colourEq_bisaturation_iff_join
    {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X)
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    {i : ι} (E F : ColourEq S i)
    (x y : X i) :
    setoidBiSaturation E.val F.val.r x y ↔
      (E.val ⊔ F.val).r x y := by
  constructor
  · rintro ⟨a,b,hxa,hab,hby⟩
    exact (E.val ⊔ F.val).trans
      ((le_sup_left : E.val ≤ E.val ⊔ F.val) hxa)
      ((E.val ⊔ F.val).trans
        ((le_sup_right : F.val ≤ E.val ⊔ F.val) hab)
        ((le_sup_left : E.val ≤ E.val ⊔ F.val) hby))
  · intro hxy
    obtain ⟨z,hxz,hzy⟩ := (sup_relation_iff S H E F x y).mp hxy
    exact ⟨z,y,hxz,hzy,E.val.refl y⟩

/-- Actual C98/E11: one and the SAME genuine SourcePhase odd old
atom c and quotient diversity atom d have exact parity image
identities with original invariant-equivalence joins, not merely
unspecified saturated relations. At zero, quotient equality pulls
back to e as required; connected X need not be RAW exact. -/
theorem originalRetainedProjectedParityJoinImages
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
    let eEq := originalExactOnCurrentSort
      A B P transport base hBase E b.val
    let K := Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b
    let Kq := originalCoherentAllparentProjectedKernel
      A B P transport tp base hBase E b.val K
        (original_retained_current_E_below_full_gate
          A B P transport tp hOne Kroot E hE b)
    ∃ (c : B.source.Atom b.val b.val)
      (d : Q.source.Atom b.val b.val),
      (∀ p q : Q.Point b.val,
        Q.source.atomRel d p q → ¬ Kq.rel p q) ∧
      (∀ p : Q.Point b.val,
        relativeIndex
          (evenColourEq Q.source Q.homogeneous d).val
          (connectivityColourEq Q.source Q.homogeneous d).val p = 2) ∧
      ∀ a z : B.Point b.val,
        (EvenWalk (Q.source.atomRel d)
            (Quotient.mk'' a : Q.Point b.val)
            (Quotient.mk'' z : Q.Point b.val) ↔
          (eEq.val.val ⊔
            (evenColourEq B.source B.homogeneous c).val).r a z) ∧
        (OddWalk (Q.source.atomRel d)
            (Quotient.mk'' a : Q.Point b.val)
            (Quotient.mk'' z : Q.Point b.val) ↔
          setoidBiSaturation eEq.val.val
            (OddWalk (B.source.atomRel c)) a z) ∧
        (ConnectedWalk (Q.source.atomRel d)
            (Quotient.mk'' a : Q.Point b.val)
            (Quotient.mk'' z : Q.Point b.val) ↔
          (eEq.val.val ⊔
            (connectivityColourEq B.source B.homogeneous c).val).r a z) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hBase E
  let eEq := originalExactOnCurrentSort
    A B P transport base hBase E b.val
  let e := originalExactCurrentKernelFamily
    A B P transport base hBase E b.val
  let K := Reached.kernel B.homogeneous
    (exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco) b
  let hNested := original_retained_current_E_below_full_gate
    A B P transport tp hOne Kroot E hE b
  let Kq := originalCoherentAllparentProjectedKernel
    A B P transport tp base hBase E b.val K hNested
  obtain ⟨c,d,_hContained,hAtomOut,_hOddOut,hIndex,hProfiles⟩ :=
    originalRetainedQuotientFullParityProfiles
      A B P transport tp hOne Kroot phase E hE b
  refine ⟨c,d,hAtomOut,hIndex,?_⟩
  intro a z
  have hEvenJoin :
      setoidBiSaturation e (EvenWalk (B.source.atomRel c)) a z ↔
        (eEq.val.val ⊔
          (evenColourEq B.source B.homogeneous c).val).r a z := by
    exact colourEq_bisaturation_iff_join B.source B.homogeneous
      eEq.val (evenColourEq B.source B.homogeneous c) a z
  have hConnJoin :
      setoidBiSaturation e (ConnectedWalk (B.source.atomRel c)) a z ↔
        (eEq.val.val ⊔
          (connectivityColourEq B.source B.homogeneous c).val).r a z := by
    exact colourEq_bisaturation_iff_join B.source B.homogeneous
      eEq.val (connectivityColourEq B.source B.homogeneous c) a z
  exact ⟨(hProfiles a z).1.trans hEvenJoin,
    (hProfiles a z).2.1,
    (hProfiles a z).2.2.trans hConnJoin⟩

end
end CCO.ExactEPGeometry
