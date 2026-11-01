import CCO.TransitionClosure.OriginalTypedCylinderStrong
import CCO.TransitionClosure.OriginalSAPTransportNoncollapse
import CCO.QuotientTransport.Composition

/-!
# B049 source07 C44-C52: atomic OLD branch suffices for canonical transport

For any nonempty ORIGINAL invariant typed RAW relation R:a→b
with R;Rᵒᵖ⊆J, and ANY original real diversity atom t
occurring in R, the old homogeneous action makes t's
complete fine orbital contained in R. Both t and R are
nonempty invariant ORIGINAL typed relations.

The true B040 canonical predecessor-class label of t is
pointwise equal to that of R on EVERY original target point.
Consequently their actual FULL invariant target kernels
are equal and their quotient bijections agree after the
proved equality congruence. This is equality of true
UNARY FUNCTIONS, not equality t=R of old fine relations.

No original SAP, CCO, NR2, hidden or quotient SAP, guessed
quotient section, source definability assumption or
atomic-path substitution is used in this generic bridge.
Full named hidden MI membership and positive branch
word presentations remain separate later tasks.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open CCO.QuotientTransport
open ParityHasse.Original

/-- A genuinely occurring ORIGINAL fine atom t within an
invariant RAW relation R is contained as its complete original-G
pair orbital, not just at one chosen representative. Original
two-point homogeneity discharges the exact full-orbit condition. -/
theorem original_invariant_raw_contains_full_atom
    (H : HomogeneousSource S G)
    {i j : ι} (R : Rel (X i) (X j))
    (hInv : Invariant (G := G) R)
    (a : S.Atom i j)
    (hAtom : a ∈ S.diversityGuard R) :
    ∀ x : X i, ∀ y : X j,
      S.atomRel a x y → R x y := by
  obtain ⟨u,v,hR,hCol⟩ := hAtom
  intro x y hXY
  obtain ⟨g,hgu,hgv⟩ :=
    S.pair_homogeneous_of_homogeneous H u x v y
      (hCol.trans hXY.symm)
  have hMoved := hInv g u v hR
  simpa only [hgu,hgv] using hMoved

/-- Source07 C44-C52 core:
for EVERY genuine OLD atom t belonging to the true original
R-diversity palette, construct its OWN genuine B040 typed
canonical transport from the SAME original E. Its labels
lambda_t and lambda_R agree POINTWISE at every target b,
its full kernel E^t=E^R holds literally, and the quotient
bijections agree after the exact kernel equality.

No claim is made that the original R menu equals {t}, or
that terminal RAW-represented quotient names are automatic.
-/
theorem original_atomic_transport_agrees_with_whole_raw
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    (R : Rel (X i) (X j))
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (a : S.Atom i j)
    (ha : a ∈ S.diversityGuard R) :
    ∃ Ta : Transport (originalColourEqAsInvEq S H J)
        (S.atomRel a),
      (∀ y : X j, Ta.label y = T.label y) ∧
      (∃ hK : Ta.target = T.target,
        ∀ q : Quotient J.val,
          InvEq.quotientCongr hK (Ta.quotientEquiv q) =
            T.quotientEquiv q) := by
  let E : InvEq G (X i) := originalColourEqAsInvEq S H J
  have hInside : ∀ x : X i, ∀ y : X j,
      S.atomRel a x y → R x y :=
    original_invariant_raw_contains_full_atom
      S H R T.invariant a ha
  have hAtomInv : Invariant (G := G) (S.atomRel a) := by
    intro g x y hXY
    exact (S.colourInvariant_of_homogeneous H g x y).trans hXY
  let Ta : Transport E (S.atomRel a) :=
    typed_quotient_transport E (S.atomRel a)
      hAtomInv (S.realized a)
      (S.original_sort_transitive_of_homogeneous H i)
      (S.original_sort_transitive_of_homogeneous H j)
      (by
        intro x z hXZ
        obtain ⟨y,hXY,hZY⟩ := hXZ
        exact T.kernel x z y
          (hInside x y hXY) (hInside z y hZY))
  have hLabels : ∀ y : X j, Ta.label y = T.label y := by
    intro y
    obtain ⟨x,hxy⟩ := Ta.coserial y
    rw [Ta.label_edge hxy, T.label_edge (hInside x y hxy)]
  have hKernels : Ta.target = T.target := by
    apply InvEq.ext
    intro y z
    change Ta.label y = Ta.label z ↔ T.label y = T.label z
    rw [hLabels y,hLabels z]
  refine ⟨Ta,hLabels,⟨hKernels,?_⟩⟩
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
      obtain ⟨y,hxy⟩ := Ta.serial x
      rw [Ta.quotientEquiv_edge hxy,
        T.quotientEquiv_edge (hInside x y hxy),
        InvEq.quotientCongr_mk]

end CCO.TransitionClosure
