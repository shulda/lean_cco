import CCO.ExactEPGeometry.OriginalQuotientIdentities
import CCO.ExactCRT.CanonicalTypedQuotients
import CCO.ExactCRT.SameSortDescent

/-!
# B062 C70: genuine one-ORIGINAL-sort RAW exact quotient descent

The original AP+HOM-CCO source may use an abstract sort type with
ONE actual sort rather than definitionally `Unit`. We retain that
source's REAL sort indices and derive the typed word-intertwining
property directly from the literal one-sort equality, original
homogeneous pair-flips and invariant RAW exact kernel relations.

For an actual ORIGINAL full RAW-exact E, make a REAL exact E-kernel
on each nominal original sort by transporting E along the proved
uniqueness of the original sort name. The previously accepted
CanonicalTyped source builds its literal quotient carriers, action
and finite occurring orbital palette.

Every nonempty original RAW-exact D which is saturated by that
actual E on BOTH sides descends to a REAL full RAW-exact relation in
the constructed one-original-sort quotient source. There is no
incorrect E<=D requirement: this also covers nonreflexive diversity
relations. The original old RAW word distribution and TI remove all
intermediate kernels, including equality letters and empty profiles.

This theorem does NOT assert mixed reverse descent for the many
independent current quotient kernels, quotient SAP, or a section of
the quotient automorphism group.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The ACTUAL old E-kernel at each nominal original sort. Every
transport uses the proved equality to the FIXED unique old carrier;
it cannot identify independently named current quotient sorts. -/
def originalExactSourceKernelFamily
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    ∀ i : A.Sorts, Setoid (A.Point i) :=
  fun i => (oldExactEqCast A.source (hOne i).symm E).val.val

/-- Each original transported E-kernel has its ACTUAL nonempty
equality-inclusive RAW exact word presentation. -/
def originalExactSourceKernelWords
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    ∀ i : A.Sorts, RawExact.NonemptyExact A.source i i :=
  fun i => Classical.choose
    (oldExactEqCast A.source (hOne i).symm E).property

/-- The old word family represents exactly the REAL transported E,
not an arbitrary invariant kernel. -/
theorem originalExactSourceKernelWords_relation
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    ∀ i : A.Sorts,
      RawExact.evaluate A.source
        (originalExactSourceKernelWords A base hOne E i).words =
      (originalExactSourceKernelFamily A base hOne E i).r := by
  intro i
  exact Classical.choose_spec
    (oldExactEqCast A.source (hOne i).symm E).property

/-- One ORIGINAL homogeneous sort, even if its name is not literally
`Unit`, supplies typed intertwinings at EVERY genuine old atomic
letter. Only in this original one-sort source is general commutation
with its invariant E-kernel valid. The result is `WordTI` for every
old RAW word, including zero-length true identity letters. -/
theorem originalOneSortWordTI
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i j : A.Sorts} (word : RawWord A.source i j) :
    CCO.ExactCRT.WordTI A.source
      (fun k => RawExact.evaluate A.source
        (originalExactSourceKernelWords A base hOne E k).words) word := by
  let W := originalExactSourceKernelWords A base hOne E
  change CCO.ExactCRT.WordTI A.source
    (fun k => RawExact.evaluate A.source (W k).words) word
  apply CCO.ExactCRT.wordTI_of_all_atoms
  intro r s a
  have hrs : r = s := (hOne r).symm.trans (hOne s)
  subst s
  exact RawSymmetric.invariant_commute _ _
    (RawExact.presentation_invariant_of_homogeneous
      A.source A.homogeneous (W r).words)
    (A.source.rawAtomRel_invariant (some a)
      (A.source.colourInvariant_of_homogeneous A.homogeneous))
    (A.source.pair_flip_of_homogeneous A.homogeneous)

/-- Source C70 at the actual one-original-sort RAW scope. The current
parent source may be abstractly indexed by a singleton type, not by
literal Unit. The only descent premise is REAL original E-bisaturation
of a nonempty old exact relation; E need not lie inside D.
Every typed quotient action/palette and full RAW exact presentation
is CONSTRUCTED from the accepted provider. -/
theorem originalOneSortExactDescent
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i : A.Sorts}
    (D : RawExact.NonemptyExact A.source i i)
    (hSat : RawExact.saturate
        (RawExact.evaluate A.source
          (originalExactSourceKernelWords A base hOne E i).words)
        (RawExact.evaluate A.source D.words)
        (RawExact.evaluate A.source
          (originalExactSourceKernelWords A base hOne E i).words) =
          RawExact.evaluate A.source D.words) :
    ∃ F : RawExact.NonemptyExact
      (CCO.ExactCRT.CanonicalTyped.source A.source A.homogeneous
        (originalExactSourceKernelFamily A base hOne E)
        (originalExactSourceKernelWords A base hOne E)
        (originalExactSourceKernelWords_relation A base hOne E)) i i,
      RawExact.evaluate
        (CCO.ExactCRT.CanonicalTyped.source A.source A.homogeneous
          (originalExactSourceKernelFamily A base hOne E)
          (originalExactSourceKernelWords A base hOne E)
          (originalExactSourceKernelWords_relation A base hOne E))
        F.words =
        CCO.ExactCRT.quotientRelation
          (CCO.ExactCRT.CanonicalTyped.projection
            (originalExactSourceKernelFamily A base hOne E) i)
          (CCO.ExactCRT.CanonicalTyped.projection
            (originalExactSourceKernelFamily A base hOne E) i)
          (RawExact.evaluate A.source D.words) := by
  let J := originalExactSourceKernelFamily A base hOne E
  let W := originalExactSourceKernelWords A base hOne E
  let hW := originalExactSourceKernelWords_relation A base hOne E
  exact CCO.ExactCRT.CanonicalTyped.typed_exact_descent
    A.source A.homogeneous J W hW A.cco D hSat
    (fun word _ => originalOneSortWordTI A base hOne E word)

/-- C70 directly for genuine FULL exact source relations. The
original nonempty RAW presentation is obtained from the accepted
`FullExact` witness in Prop; no extra word provider or E<=D
premise is supplied. Its image is FULL RAW exact on the ACTUAL
original canonical E-quotient source. -/
theorem originalOneSortFullExactDescent
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i : A.Sorts}
    (R : TRel A.Point i i)
    (hExact : FullExact A.source R)
    (hSat : RawExact.saturate
      (RawExact.evaluate A.source
        (originalExactSourceKernelWords A base hOne E i).words)
      R
      (RawExact.evaluate A.source
        (originalExactSourceKernelWords A base hOne E i).words) = R) :
    FullExact
      (CCO.ExactCRT.CanonicalTyped.source A.source A.homogeneous
        (originalExactSourceKernelFamily A base hOne E)
        (originalExactSourceKernelWords A base hOne E)
        (originalExactSourceKernelWords_relation A base hOne E))
      (CCO.ExactCRT.quotientRelation
        (CCO.ExactCRT.CanonicalTyped.projection
          (originalExactSourceKernelFamily A base hOne E) i)
        (CCO.ExactCRT.CanonicalTyped.projection
          (originalExactSourceKernelFamily A base hOne E) i) R) := by
  obtain ⟨D,hD⟩ := hExact
  have hSatD : RawExact.saturate
      (RawExact.evaluate A.source
        (originalExactSourceKernelWords A base hOne E i).words)
      (RawExact.evaluate A.source D.words)
      (RawExact.evaluate A.source
        (originalExactSourceKernelWords A base hOne E i).words) =
        RawExact.evaluate A.source D.words := by
    simpa only [hD] using hSat
  obtain ⟨F,hF⟩ :=
    originalOneSortExactDescent A base hOne E D hSatD
  refine ⟨F,?_⟩
  exact hF.trans (congrArg
    (CCO.ExactCRT.quotientRelation
      (CCO.ExactCRT.CanonicalTyped.projection
        (originalExactSourceKernelFamily A base hOne E) i)
      (CCO.ExactCRT.CanonicalTyped.projection
        (originalExactSourceKernelFamily A base hOne E) i)) hD)

end
end CCO.ExactEPGeometry
