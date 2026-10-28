import CCO.RawExact.ExactCalculusSource
import CCO.RawExact.ActualOrbitalExact
import CCO.RawSource
import Mathlib.Data.Fintype.Powerset

/-! Original FULL identity-inclusive RAW exact relations. The only abstract
calculus input for bridge geometry is nonempty exact convolution; the original
homogeneous CCO source supplies it below. No quotient descent is implicit. -/

universe u v w t
namespace CCO.RigidGroupoid.Geometry

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def FullExact {i j : ι} (R : TRel X i j) : Prop :=
  ∃ D : RawExact.NonemptyExact S i j, RawExact.evaluate S D.words = R

structure ExactCalculus : Prop where
  comp : ∀ {i j k : ι} {R : TRel X i j} {T : TRel X j k},
    FullExact S R → FullExact S T → FullExact S (TRel.comp R T)

theorem FullExact.nonempty {i j : ι} {R : TRel X i j}
    (h : FullExact S R) : TRel.Nonempty R := by
  obtain ⟨D,rfl⟩ := h
  exact D.nonempty

theorem fullExact_converse {i j : ι} {R : TRel X i j}
    (h : FullExact S R) : FullExact S (TRel.converse R) := by
  obtain ⟨D,rfl⟩ := h
  exact ⟨D.converse S, RawExact.evaluate_reverse S D.words⟩

theorem fullExact_identity (i : ι) : FullExact S (TRel.ident X i) :=
  ⟨RawExact.exactIdentityAtom S i, RawExact.exactIdentityAtom_relation S i⟩

theorem fullExact_top (i j : ι) : FullExact S (TRel.top X i j) :=
  ⟨RawExact.NonemptyExact.top S i j, RawExact.evaluate_nil S⟩

theorem fullExact_actual_atom {i j : ι} (x : X i) (y : X j) :
    FullExact S (S.rawAtomRel (S.colour x y)) := RawExact.actual_pair_colour_exact S x y

theorem fullExact_meet {i j : ι} {R T : TRel X i j}
    (hR : FullExact S R) (hT : FullExact S T)
    (hn : TRel.Nonempty (fun x y => R x y ∧ T x y)) :
    FullExact S (fun x y => R x y ∧ T x y) := by
  obtain ⟨D,rfl⟩ := hR
  obtain ⟨F,rfl⟩ := hT
  exact ⟨D.meet S F hn, RawExact.evaluate_append S D.words F.words⟩

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)

include H

theorem FullExact.invariant {i j : ι} {R : TRel X i j}
    (h : FullExact S R) : TRel.Invariant (G := G) R := by
  obtain ⟨D,rfl⟩ := h
  exact RawExact.presentation_invariant_of_homogeneous S H D.words

theorem FullExact.serial {i j : ι} {R : TRel X i j}
    (h : FullExact S R) : TRel.Serial R :=
  S.raw_serial_of_homogeneous H R (h.nonempty S) (h.invariant S H)

theorem FullExact.coserial {i j : ι} {R : TRel X i j}
    (h : FullExact S R) : TRel.Coserial R :=
  S.raw_coserial_of_homogeneous H R (h.nonempty S) (h.invariant S H)

theorem invariant_same_sort_converse {i : ι} (R : TRel X i i)
    (hR : TRel.Invariant (G := G) R) : TRel.converse R = R := by
  funext x y
  apply propext
  constructor
  · intro hyx
    obtain ⟨g,hgy,hgx⟩ := S.pair_flip_of_homogeneous H y x
    simpa only [hgy,hgx] using hR g y x hyx
  · intro hxy
    change R y x
    obtain ⟨g,hgx,hgy⟩ := S.pair_flip_of_homogeneous H x y
    simpa only [hgx,hgy] using hR g x y hxy

theorem FullExact.same_sort_converse {i : ι} {R : TRel X i i}
    (h : FullExact S R) : TRel.converse R = R :=
  invariant_same_sort_converse S H R (h.invariant S H)

theorem exactCalculus_of_homogeneous_CCO
    (cco : SemanticCCO.{u,v,max u v,w} S) : ExactCalculus S where
  comp := by
    intro i j k R T hR hT
    obtain ⟨D,rfl⟩ := hR
    obtain ⟨F,rfl⟩ := hT
    exact ⟨RawExact.convolutionExact S H D F,
      RawExact.convolutionExact_represents S H
        (RawExact.heterogeneousExactBallHelly_of_CCO S H cco) D F⟩

/-- Finite ACTUAL optional orbital supports make the collection of original
full exact relations finite, independently of any finite-index theorem. -/
theorem finite_fullExact (i j : ι) : Finite {R : TRel X i j // FullExact S R} := by
  classical
  letI : Fintype (S.Atom i j) := S.finiteAtom i j
  let f : {R : TRel X i j // FullExact S R} → Set (Option (S.Atom i j)) :=
    fun R => S.rawSupport R.val
  apply Finite.of_injective f
  intro R T h
  apply Subtype.ext
  have hR := S.invariant_support_representation_of_homogeneous H R.val (R.property.invariant S H)
  have hT := S.invariant_support_representation_of_homogeneous H T.val (T.property.invariant S H)
  exact hR.symm.trans ((congrArg S.representedSupport h).trans hT)

end CCO.RigidGroupoid.Geometry
