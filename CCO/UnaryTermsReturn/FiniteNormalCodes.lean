import CCO.UnaryTermsReturn.RealSourceKernel

/-!
# B052 C11–C13 — finite uniform ORIGINAL normal-pattern code family

B049 has a finite family of *actual* original RAW unary normal data
between every pair of named original sorts. Since the set of source
sorts is finite too, their dependent disjoint union is a finite
semantic code family, independent of the actual input vertex,
of the length of any named unary expression, and of the size of any
original or quotient carrier.

Every normal datum has an ACTUAL input equivalence E, source
coarsening E<=J, an invariant nonempty RAW relation R and its
canonical B040 target kernel F. Evaluation at a real point is
defined on the true quotient carriers and returns its true tagged
FULL target coordinate. This is a finite OVERESTIMATE for the
source10 unary function closure; it does not postulate that an
arbitrary total-unary partial source is interpretable in M.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- Genuine fixed-source ORIGINAL normal data across ALL named
target old sorts, retaining their exact interpreted quotient map. -/
abbrev OriginalSourceNormalCode (i : ι) :=
  Σ j : ι, OriginalCanonicalUnaryNormalDatum S (G := G) i j

/-- Genuine all-source, all-target ORIGINAL normal code family.
This records the ORIGINAL real sort of each starting point,
and hence does not silently identify distinct typed carriers. -/
abbrev OriginalAllNormalCodes :=
  Σ i : ι, OriginalSourceNormalCode S (G := G) i

/-- Finite original named sorts and the REAL finite full old-G
RAW relation family make the normal-code type FINITE.
No syntactic bound or finite original/quasi-quotient carrier. -/
theorem original_source_normal_codes_finite
    (H : HomogeneousSource S G) (i : ι) :
    Finite (OriginalSourceNormalCode S (G := G) i) := by
  letI : Fintype ι := S.finiteSort
  haveI (j : ι) :
      Finite (OriginalCanonicalUnaryNormalDatum S (G := G) i j) :=
    originalCanonicalUnaryNormalDatum_finite S H
  infer_instance

/-- The all-source version is likewise a genuinely finite
DEPENDENT data family, not a single bounded syntax grammar. -/
theorem original_all_normal_codes_finite
    (H : HomogeneousSource S G) :
    Finite (OriginalAllNormalCodes S (G := G)) := by
  letI : Fintype ι := S.finiteSort
  haveI (i : ι) :
      Finite (OriginalSourceNormalCode S (G := G) i) :=
    original_source_normal_codes_finite S H i
  infer_instance

/-- An explicit nonzero finite number depending only on the
fixed interpreted original type/RAW relation tables. It includes
a spare slot for the REAL identity, which is not a hidden quotient
projection or artificial STRONG identity atom. The proof that
it bounds all actual one-generated hidden closures is separate. -/
noncomputable def originalSourceUniformNormalCodeBudget
    (H : HomogeneousSource S G) : Nat :=
  Nat.card (OriginalAllNormalCodes S (G := G)) + 1

theorem originalSourceUniformNormalCodeBudget_pos
    (H : HomogeneousSource S G) :
    0 < originalSourceUniformNormalCodeBudget S H :=
  Nat.zero_lt_succ _

/-- Actual old FULL quotient target values retain BOTH the old
sort name and the exact invariant equivalence, not merely a
numerical orbit or an independently chosen hidden section. -/
abbrev OriginalNormalCodeTargetValue :=
  Σ j : ι, Σ F : ColourEq S j, Quotient F.val

/-- Evaluate one genuine RAW normal datum at an ACTUAL real
point by first taking its source E-class and then its original
canonical quotient function. The target is tagged by its real
old sort and exact transported FULL kernel. -/
noncomputable def originalSourceNormalCodeValue
    (H : HomogeneousSource S G)
    {i : ι} (x : X i)
    (c : OriginalSourceNormalCode S (G := G) i) :
    OriginalNormalCodeTargetValue S :=
  ⟨c.1, ⟨(originalCanonicalUnaryNormalDatum_function S H c.2).2.1,
    (originalCanonicalUnaryNormalDatum_function S H c.2).2.2
      (Quotient.mk c.2.val.1.val x)⟩⟩

/-- Regardless of the size of the ambient real/hidden carriers,
the actual values of *all finite normal CODES* from x form
a finite set because the fixed original normal data are finite. -/
theorem original_source_normal_code_values_finite
    (H : HomogeneousSource S G)
    {i : ι} (x : X i) :
    (Set.range (originalSourceNormalCodeValue S H x)).Finite := by
  letI : Finite (OriginalSourceNormalCode S (G := G) i) :=
    original_source_normal_codes_finite S H i
  exact Set.finite_range _

end CCO.UnaryTermsReturn
