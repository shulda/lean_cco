import CCO.ExactEPGeometry.DiscardedQuotientClassEquiv
import CCO.ExactEPGeometry.OriginalExactOccupancy
import CCO.APCharacter.SourceAge.SingleStep

/-!
# B062 C104: canonical original E-class carrier across actual unary histories

A TRUE unary reduct identifies the entire tagged source carrier
bijectively. Pulling back a fixed ORIGINAL full RAW-exact equivalence
along the ACTUAL composed reduct preserves the genuine global
quotient of original E-classes: all stages have the same E-classes,
even though their current named sorts and binary presentations change.

The proof uses literal UnaryReduct composition and the genuine
point-bijection required by each source transition; its quotient map
is not a new automorphism-group section. In particular it does NOT
identify current quotient orbital palettes or prove the full safe
marked age at retained/discarded stages. Those are separate
C96/C103–C104 obligations.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Under ANY REAL additional unary reduct of true current sources,
the actual whole-original-E class quotient is preserved through
the composed old-to-new projection. This statement uses the entire
old original E (not a one-parent local surrogate), and the point
map is genuinely bijective on all tagged carriers. -/
noncomputable def originalGlobalEclassEquivAlongReduct
    (A B C : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (R : UnaryReduct B.source C.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    Quotient (currentOriginalExactSetoid A C
      (P.compose R) base hOne E) ≃
    Quotient (currentOriginalExactSetoid A B P base hOne E) := by
  let S := currentOriginalExactSetoid A C
    (P.compose R) base hOne E
  let T := currentOriginalExactSetoid A B P base hOne E
  let f : Sigma C.Point → Sigma B.Point := R.project
  have hPull : ∀ x y : Sigma C.Point,
      S x y ↔ T (f x) (f y) := by
    intro x y
    rfl
  have hSurj : ∀ y : Sigma B.Point,
      ∃ x : Sigma C.Point, T y (f x) := by
    intro y
    obtain ⟨x,hx⟩ := R.bijective.2 y
    refine ⟨x,?_⟩
    change T y (R.project x)
    change R.project x = y at hx
    simpa only [hx] using (T.refl y)
  exact quotientClassEquiv_of_classwiseSurjective S T f hPull hSurj

/-- This equivalence is the LITERAL class-map of the true current
unary projection, with no representative or quotient-section choice. -/
theorem originalGlobalEclassEquivAlongReduct_mk
    (A B C : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (R : UnaryReduct B.source C.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (x : Sigma C.Point) :
    originalGlobalEclassEquivAlongReduct
      A B C P R base hOne E (Quotient.mk'' x) =
    (Quotient.mk'' (R.project x) :
      Quotient (currentOriginalExactSetoid A B P base hOne E)) := rfl

/-- Concrete one-step C104 instance on the ACTUAL complete
SourcePhase successor, valid for either retained or discarded E:
the phase changes labels but not ORIGINAL global E-classes. -/
noncomputable def originalPhaseGlobalEclassEquiv
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    Quotient (currentOriginalExactSetoid A
      (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase))
      base hOne E) ≃
    Quotient (currentOriginalExactSetoid A B P base hOne E) :=
  originalGlobalEclassEquivAlongReduct
    A B (SingleStep.successor B phase)
      P (SingleStep.projection B phase) base hOne E

/-- C104 full-history CARRIER invariant: any genuine finite
history of actual named-sort and age transitions transports
precisely the original global E-classes to its current prefix.
The history itself is actual source data, not a hypothetical
quotient safe history. This theorem says nothing about the
full quotient binary age, characters, gates, or maximality. -/
noncomputable def originalGlobalEclassEquivActualHistory
    (A B : CurrentSource.{u,v,w,t})
    (history : History (fun X Y =>
      Nonempty (CurrentSource.ActualStep X Y)) A B)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    Quotient (currentOriginalExactSetoid A B
      (CurrentSource.historyReduct history) base hOne E) ≃
    Quotient (currentOriginalExactSetoid A A
      (UnaryReduct.identity A.source) base hOne E) :=
  originalGlobalEclassEquivAlongReduct
    A A B (UnaryReduct.identity A.source)
      (CurrentSource.historyReduct history) base hOne E

end
end CCO.ExactEPGeometry
