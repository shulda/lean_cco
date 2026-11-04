import CCO.ExactEPGeometry.OriginalGlobalEclassHistory
import CCO.ExactEPGeometry.OriginalDiscardedSaturatedOldPair

/-!
# B062 C104: full ORIGINAL quotient binary blocks along actual source histories

The actual full tagged-point map of EVERY true UnaryReduct is bijective.
Thus a fixed original E-saturation E;D;E of ANY original binary
predicate D pulls back to exactly the saturation of the corresponding
original predicate at every actual unary prefix.

We descend this equality to the TRUE quotient carrier of global
original E-classes, not to a pointwise section or a chosen local
K/E gate. It includes actual logical E-diagonal as one case and all
original atomic pair predicates as others. This is the ORIGINAL
quotient binary palette along the existing history. It does NOT
establish that the new marked CurrentSource quotient has no finer
binary orbital names or the complete C96/C103–C104 finite age.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers

noncomputable section

/-- Any whole-S saturated binary predicate is canonically a
predicate on TRUE S-classes: a representative exists iff the
saturated relation holds on any other representatives. In
particular this does not identify distinct logical E-classes. -/
def fullSaturationOnClasses {X : Type u}
    (S : Setoid X) (D : X → X → Prop)
    (q r : Quotient S) : Prop :=
  ∃ x y : X,
    (Quotient.mk'' x : Quotient S) = q ∧
    (Quotient.mk'' y : Quotient S) = r ∧
    setoidSaturation S D x y

theorem fullSaturationOnClasses_mk {X : Type u}
    (S : Setoid X) (D : X → X → Prop) (x y : X) :
    fullSaturationOnClasses S D
      (Quotient.mk'' x) (Quotient.mk'' y) ↔
        setoidSaturation S D x y := by
  constructor
  · rintro ⟨x',y',hx,hy,hD⟩
    have hxx : S.r x x' := Quotient.exact hx.symm
    have hyy : S.r y y' := Quotient.exact hy.symm
    exact (setoidSaturation_congr S D hxx hyy).mpr hD
  · intro hD
    exact ⟨x,y,rfl,rfl,hD⟩

/-- C104 binary ORIGINAL block preservation on every pair of real
new/current tagged points. Source reduct bijectivity is used in
the reverse direction to lift both WHOLE E;D;E witnesses, not just
a single point from each class or a convenient atomic representative.
No SAP or phase character is required. -/
theorem originalGlobalSaturatedPair_preserved_reduct
    (A B C : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (R : UnaryReduct B.source C.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (D : Sigma A.Point → Sigma A.Point → Prop)
    (a b : Sigma C.Point) :
    let S := currentOriginalExactSetoid A C (P.compose R) base hOne E
    let T := currentOriginalExactSetoid A B P base hOne E
    setoidSaturation S
      (fun x y => D ((P.compose R).project x) ((P.compose R).project y))
      a b ↔
    setoidSaturation T
      (fun x y => D (P.project x) (P.project y))
      (R.project a) (R.project b) := by
  let S := currentOriginalExactSetoid A C (P.compose R) base hOne E
  let T := currentOriginalExactSetoid A B P base hOne E
  let f : Sigma C.Point → Sigma B.Point := R.project
  have hPull (x y : Sigma C.Point) :
      S x y ↔ T (f x) (f y) := Iff.rfl
  change setoidSaturation S
      (fun x y => D (P.project (f x)) (P.project (f y))) a b ↔
    setoidSaturation T
      (fun x y => D (P.project x) (P.project y)) (f a) (f b)
  constructor
  · rintro ⟨x,y,hax,hD,hyb⟩
    exact ⟨f x,f y,(hPull a x).mp hax,hD,(hPull y b).mp hyb⟩
  · rintro ⟨x,y,hax,hD,hyb⟩
    obtain ⟨xx,hxx⟩ := R.bijective.2 x
    obtain ⟨yy,hyy⟩ := R.bijective.2 y
    change f xx = x at hxx
    change f yy = y at hyy
    refine ⟨xx,yy,?_,?_,?_⟩
    · exact (hPull a xx).mpr (by simpa only [hxx] using hax)
    · simpa only [hxx,hyy] using hD
    · exact (hPull yy b).mpr (by simpa only [hyy] using hyb)

/-- This is the true quotient-level C104 statement: the canonical
equivalence of global ORIGINAL E-classes preserves and REFLECTS
EVERY original E;D;E binary relation. The conclusion is on the
literal quotient types, not merely on selected representatives. -/
theorem originalGlobalEclassEquiv_preserves_originalSaturatedPair
    (A B C : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (R : UnaryReduct B.source C.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (D : Sigma A.Point → Sigma A.Point → Prop)
    (q r : Quotient (currentOriginalExactSetoid A C
        (P.compose R) base hOne E)) :
    let S := currentOriginalExactSetoid A C (P.compose R) base hOne E
    let T := currentOriginalExactSetoid A B P base hOne E
    let Dnew : Sigma C.Point → Sigma C.Point → Prop :=
      fun x y => D ((P.compose R).project x) ((P.compose R).project y)
    let Dold : Sigma B.Point → Sigma B.Point → Prop :=
      fun x y => D (P.project x) (P.project y)
    fullSaturationOnClasses S Dnew q r ↔
      fullSaturationOnClasses T Dold
        (originalGlobalEclassEquivAlongReduct
          A B C P R base hOne E q)
        (originalGlobalEclassEquivAlongReduct
          A B C P R base hOne E r) := by
  let S := currentOriginalExactSetoid A C (P.compose R) base hOne E
  let T := currentOriginalExactSetoid A B P base hOne E
  let Dnew : Sigma C.Point → Sigma C.Point → Prop :=
    fun x y => D ((P.compose R).project x) ((P.compose R).project y)
  let Dold : Sigma B.Point → Sigma B.Point → Prop :=
    fun x y => D (P.project x) (P.project y)
  change fullSaturationOnClasses S Dnew q r ↔
    fullSaturationOnClasses T Dold
      (originalGlobalEclassEquivAlongReduct
        A B C P R base hOne E q)
      (originalGlobalEclassEquivAlongReduct
        A B C P R base hOne E r)
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      rw [originalGlobalEclassEquivAlongReduct_mk
        A B C P R base hOne E x,
          originalGlobalEclassEquivAlongReduct_mk
        A B C P R base hOne E y]
      exact (fullSaturationOnClasses_mk S Dnew x y).trans
        ((originalGlobalSaturatedPair_preserved_reduct
          A B C P R base hOne E D x y).trans
          (fullSaturationOnClasses_mk T Dold
            (R.project x) (R.project y)).symm)

/-- Along the COMPLETE actual finite source history, the fixed
original E quotient retains the ENTIRE old original E-saturated
binary palette, including equality and all genuinely realized old
diversity atoms. No assertion about new marked quotient orbital
refinements or its full finite age is inferred. -/
theorem originalHistoryEclassOriginalPair_preserved
    (A B : CurrentSource.{u,v,w,t})
    (history : History (fun X Y =>
      Nonempty (CurrentSource.ActualStep X Y)) A B)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (D : Sigma A.Point → Sigma A.Point → Prop)
    (q r : Quotient (currentOriginalExactSetoid A B
      (CurrentSource.historyReduct history) base hOne E)) :
    let P := UnaryReduct.identity A.source
    let R := CurrentSource.historyReduct history
    let S := currentOriginalExactSetoid A B (P.compose R) base hOne E
    let T := currentOriginalExactSetoid A A P base hOne E
    let Dnew : Sigma B.Point → Sigma B.Point → Prop :=
      fun x y => D ((P.compose R).project x) ((P.compose R).project y)
    let Dold : Sigma A.Point → Sigma A.Point → Prop :=
      fun x y => D (P.project x) (P.project y)
    fullSaturationOnClasses S Dnew q r ↔
      fullSaturationOnClasses T Dold
        (originalGlobalEclassEquivActualHistory
          A B history base hOne E q)
        (originalGlobalEclassEquivActualHistory
          A B history base hOne E r) := by
  exact originalGlobalEclassEquiv_preserves_originalSaturatedPair
    A A B (UnaryReduct.identity A.source)
      (CurrentSource.historyReduct history)
        base hOne E D q r

end
end CCO.ExactEPGeometry
