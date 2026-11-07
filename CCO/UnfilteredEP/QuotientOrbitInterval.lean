import CCO.UnfilteredEP.QuotientHolonomy
import CCO.ParityHasse.Original.RelativeIndices
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Lean.Elab.Tactic.Omega

/-! A genuine cyclic orbit equivalence upstairs in the FULL original
invariant lattice. A nonidentity equivariant quotient permutation yields
a strict finite-relative-index interval. No order/Ramsey/EP input occurs. -/

universe u v w r
namespace CCO.UnfilteredEP
open CCO.ParityHasse.Original CCO.TerminalLattice CCO.AutomaticEPCore
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) {i : ι} (J : ColourEq S i)

abbrev QuotientCyclicGroup (f : QuotientFunctionalGroup S H J) := ↥(Subgroup.zpowers f)

def quotientCyclicSetoid (f : QuotientFunctionalGroup S H J) : Setoid (X i) := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  exact Setoid.comap (Quotient.mk J.val)
    (MulAction.orbitRel (QuotientCyclicGroup S H J f) (Quotient J.val))

theorem quotientCyclicSetoid_invariant (f : QuotientFunctionalGroup S H J)
    (g : G) (x y : X i) :
    quotientCyclicSetoid S H J f x y → quotientCyclicSetoid S H J f (g • x) (g • y) := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  rintro ⟨a,ha⟩
  refine ⟨a,?_⟩
  change a.val.val (Quotient.mk J.val (g • y)) = Quotient.mk J.val (g • x)
  rw [← originalQuotient_mk_smul S H J,← originalQuotient_mk_smul S H J]
  exact (a.val.property g _).trans (congrArg (fun q => g • q) ha)

def quotientCyclicFullEq (f : QuotientFunctionalGroup S H J) : ColourEq S i :=
  ⟨quotientCyclicSetoid S H J f,by
    intro x y x' y' hc
    obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' hc
    constructor
    · intro h
      simpa only [hgx,hgy] using quotientCyclicSetoid_invariant S H J f g x y h
    · intro h
      have hm := quotientCyclicSetoid_invariant S H J f g⁻¹ x' y' h
      simpa only [← hgx,← hgy,inv_smul_smul] using hm⟩

theorem le_quotientCyclicFullEq (f : QuotientFunctionalGroup S H J) :
    J ≤ quotientCyclicFullEq S H J f := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  intro x y hxy
  change MulAction.orbitRel (QuotientCyclicGroup S H J f) (Quotient J.val)
    (Quotient.mk J.val x) (Quotient.mk J.val y)
  rw [Quotient.sound hxy]

def cyclicRelativeToOrbit (f : QuotientFunctionalGroup S H J) (a : X i) :
    RelativeClass J.val (quotientCyclicFullEq S H J f).val a →
      {q : Quotient J.val //
        letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
        q ∈ MulAction.orbit (QuotientCyclicGroup S H J f) (Quotient.mk J.val a)} := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  refine Quotient.lift (fun x => ⟨Quotient.mk J.val x.val,?_⟩) ?_
  · exact MulAction.mem_orbit_symm.mp x.property
  · intro x y hxy
    exact Subtype.ext (Quotient.sound hxy)

theorem cyclicRelativeToOrbit_injective (f : QuotientFunctionalGroup S H J) (a : X i) :
    Function.Injective (cyclicRelativeToOrbit S H J f a) := by
  intro q t
  refine Quotient.inductionOn₂ q t ?_
  intro x y h
  apply Quotient.sound
  have hv := congrArg Subtype.val h
  change Quotient.mk J.val x.val = Quotient.mk J.val y.val at hv
  exact (Quotient.exact hv : J.val x.val y.val)

theorem quotientCyclicFullEq_finite_relative (f : QuotientFunctionalGroup S H J) (a : X i) :
    Finite (RelativeClass J.val (quotientCyclicFullEq S H J f).val a) := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  letI := quotient_functional_group_finite S H J
  letI : Finite (QuotientCyclicGroup S H J f) := inferInstance
  letI : Finite ↥(MulAction.orbit (QuotientCyclicGroup S H J f) (Quotient.mk J.val a)) :=
    (Finite.finite_mulAction_orbit (Quotient.mk J.val a)).to_subtype
  exact Finite.of_injective _ (cyclicRelativeToOrbit_injective S H J f a)

theorem quotientCyclicFullEq_strict (f : QuotientFunctionalGroup S H J) (hf : f ≠ 1) :
    J < quotientCyclicFullEq S H J f := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  apply lt_of_le_of_ne (le_quotientCyclicFullEq S H J f)
  intro he
  apply hf
  apply Subtype.ext
  apply Equiv.ext
  intro q
  induction q using Quotient.inductionOn with | _ x =>
    obtain ⟨y,hy⟩ := Quotient.exists_rep (f.val (Quotient.mk J.val x))
    have hk : quotientCyclicFullEq S H J f x y := by
      apply MulAction.mem_orbit_symm.mp
      exact ⟨⟨f,Subgroup.mem_zpowers f⟩,hy.symm⟩
    have hJ : J x y := he ▸ hk
    exact hy.symm.trans (Quotient.sound (J.val.symm hJ))

/-- C32: the cyclic orbit interval is an ACTUAL strict FULL interval,
with one finite relative cardinal (constant on the transitive sort). -/
theorem quotient_nontrivial_finite_interval (f : QuotientFunctionalGroup S H J) (hf : f ≠ 1) :
    ∃ K : ColourEq S i, J < K ∧
      (∀ a, Finite (RelativeClass J.val K.val a)) ∧
      (∀ a, 1 < relativeIndex J.val K.val a) ∧
      (∀ a b, relativeIndex J.val K.val a = relativeIndex J.val K.val b) := by
  let K := quotientCyclicFullEq S H J f
  have hJK : J < K := quotientCyclicFullEq_strict S H J f hf
  refine ⟨K,hJK,quotientCyclicFullEq_finite_relative S H J f,?_,?_⟩
  · intro a
    letI := quotientCyclicFullEq_finite_relative S H J f a
    have hp : 0 < relativeIndex J.val K.val a := Nat.card_pos
    have hn : relativeIndex J.val K.val a ≠ 1 := by
      intro he
      exact hJK.ne ((relativeIndex_eq_one_iff S H J K hJK.le a).mp he)
    omega
  · exact relativeIndex_uniform S H J K

end
end CCO.UnfilteredEP
