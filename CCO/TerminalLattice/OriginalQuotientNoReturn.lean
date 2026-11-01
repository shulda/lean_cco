import CCO.TerminalLattice.OriginalQuotientPositiveHelly
import CCO.TerminalLattice.FullCoverAlternation
import CCO.TerminalLattice.FullCoverUniformPowers

/-!
# B050 source09 OWL: no quotient-diagonal-only product with an external orbital

For a FULL original invariant cover J ⋖ K outside local index two,
an external COMPLETE quotient orbital of the ORIGINAL group G has
eventual full positive quotient powers, including honest returns.
We prove directly that composing it with ANY serial quotient relation
cannot be supported only on the quotient diagonal.

If its composition with a serial relation T had only diagonal
outputs, the symmetry of the original complete orbital would force
its graph to be a perfect matching. Its genuine quotient square
would then be equality, so its positive even powers would remain
the true quotient diagonal. This contradicts the ALREADY PROVED
CCO-free eventual full quotient powers, evaluated at the actual
external root pair.

No quotient automorphism group, original CCO, SAP/NR2 assumption,
positive old identity atom, or assertion that T is a complete
orbital or excludes the quotient diagonal. It is enough that T
is SERIAL. This is the exact no-return input for a nonempty
product of external orbitals, with all real diagonal states retained.
-/

universe u v w t

namespace CCO.TerminalLattice

open ParityHasse.Original

/-- Two serial quotient relations compose to another serial relation
using one actual intermediate quotient vertex. No finiteness,
symmetry, group action, or equality-free assumption. -/
theorem original_quotient_serial_comp
    {Q : Type*} (R T : Q → Q → Prop)
    (hR : ∀ q, ∃ r, R q r)
    (hT : ∀ q, ∃ r, T q r) :
    ∀ q, ∃ r, RawSymmetric.compose R T q r := by
  intro q
  obtain ⟨mid,hm⟩ := hR q
  obtain ⟨r,hr⟩ := hT mid
  exact ⟨r,mid,hm,hr⟩

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- SOURCE09 OWL no-return, with a REAL original-G external pair:
a complete external quotient orbital, followed by ANY SERIAL
quotient relation, has at least one OFF-DIAGONAL quotient output.
The second relation need not be invariant, symmetric, positive,
complete or irreflexive.

This is a CCO-free consequence of the source's FULL-cover and
non-index-two hypotheses: a diagonal-only output would make the
first symmetric orbital have square equal to TRUE quotient equality,
contradicting its proved eventual FULL quotient powers. -/
theorem original_external_orbital_serial_comp_has_offdiagonal
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i)
    (hJK : J ⋖ K)
    (anchor : X i)
    (hNotTwo : relativeIndex J.val K.val anchor ≠ 2)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (T : Quotient J.val → Quotient J.val → Prop)
    (hSerialT : ∀ q : Quotient J.val, ∃ r, T q r) :
    ∃ q r : Quotient J.val, q ≠ r ∧
      RawSymmetric.compose
        (originalQuotientOrbital S (G := G) J a b) T q r := by
  let R : Quotient J.val → Quotient J.val → Prop :=
    originalQuotientOrbital S (G := G) J a b
  by_contra hNo
  have hDiagonal : ∀ q r : Quotient J.val,
      RawSymmetric.compose R T q r → q = r := by
    intro q r hqr
    by_contra hneq
    exact hNo ⟨q,r,hneq,hqr⟩
  have hUnique (p q r : Quotient J.val)
      (hpq : R p q) (hpr : R p r) : q = r := by
    obtain ⟨z,hTz⟩ := hSerialT p
    have hqp : R q p :=
      originalQuotientOrbital_symmetric S H J a b p q hpq
    have hrp : R r p :=
      originalQuotientOrbital_symmetric S H J a b p r hpr
    have hqz : q = z := hDiagonal q z ⟨p,hqp,hTz⟩
    have hrz : r = z := hDiagonal r z ⟨p,hrp,hTz⟩
    exact hqz.trans hrz.symm
  have hSquare : relPow R 2 = Eq := by
    funext q r
    apply propext
    constructor
    · intro hWalk
      obtain ⟨mid,hqmid,hmr⟩ := hWalk
      have hmQ : R mid q :=
        originalQuotientOrbital_symmetric S H J a b q mid hqmid
      have hmR : R mid r := (relPow_one R mid r).mp hmr
      exact hUnique mid q r hmQ hmR
    · intro hEq
      subst r
      obtain ⟨mid,hqm⟩ :=
        originalQuotientOrbital_serial S H J a b q
      exact ⟨mid,hqm,(relPow_one R mid q).mpr
        (originalQuotientOrbital_symmetric S H J a b q mid hqm)⟩
  have hLocalNotTwo : relativeIndex J.val K.val a ≠ 2 := by
    intro hTwo
    have hIndex : relativeIndex J.val K.val a =
        relativeIndex J.val K.val anchor :=
      relativeIndex_uniform S H J K a anchor
    exact hNotTwo (hIndex.symm.trans hTwo)
  obtain ⟨N,hN,hFull⟩ :=
    originalQuotient_uniform_full_powers
      S H J K hJK a b hab hne hLocalNotTwo
  have hFullPair :
      originalUpperSetoid S J K hJK.le
        (Quotient.mk J.val a) (Quotient.mk J.val b) :=
    (originalUpperSetoid_mk S J K hJK.le a b).mpr hab
  have hWalk : relPow R (2*(N+1)+2)
      (Quotient.mk J.val a) (Quotient.mk J.val b) := by
    exact (hFull (2*(N+1)+2) (by omega) _ _).mpr hFullPair
  have hEven : relPow R (2*(N+1)+2) = Eq :=
    (relPow_alternating_of_square R hSquare (N+1)).2
  rw [hEven] at hWalk
  exact hne (Quotient.exact hWalk)

end CCO.TerminalLattice
