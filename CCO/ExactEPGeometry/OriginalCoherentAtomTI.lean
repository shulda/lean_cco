import CCO.ExactEPGeometry.OriginalCurrentTypedQuotients
import CCO.ExactEPGeometry.OriginalOneSortExactDescent
import CCO.ExactEPGeometry.ExactTraceProduct
import CCO.ExactCRT.Intertwining

/-!
# B062 C82: typed atom intertwining for one ORIGINAL exact E

The simultaneous quotient provider cannot descend arbitrary
E-bisaturated mixed exact relations when its kernels are chosen
independently at many current sorts. Here they are NOT independent:
each current kernel is the genuine exact trace of the SAME full
RAW-exact equivalence E on one original homogeneous symmetric sort.

The already proved guarded (TP) of the genuine old-to-current
certified prefix, together with original ONE-sort exact word
intertwining, proves the correctly typed current atom equations
  e_i ; a_ij = a_ij ; e_j.
Both TP calls have real current nonempty witnesses in their exact
displayed middle sorts. No quotient SAP or quotient action section
is used. The derivation does not assert TI for arbitrary independent
current quotient kernels.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Every ACTUAL current diversity atom is literally the trace
of its named old atom under the original-to-current UnaryReduct.
The injective atomic name map prevents an old atom from
collapsing two different current atomic colours. -/
theorem original_current_atom_old_trace
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    {i j : B.Sorts} (a : B.source.Atom i j)
    (x : B.Point i) (y : B.Point j) :
    A.source.atomRel (P.atom i j a) (P.point i x) (P.point j y) ↔
      B.source.atomRel a x y := by
  change A.source.colour (P.point i x) (P.point j y) =
      some (P.atom i j a) ↔ B.source.colour x y = some a
  rw [P.colour]
  constructor
  · intro h
    cases hcol : B.source.colour x y with
    | none =>
        simp only [hcol, Option.map_none] at h
        contradiction
    | some b =>
        have hab : P.atom i j b = P.atom i j a := by
          simpa only [hcol, Option.map_some, Option.some.injEq] using h
        have hba : b = a := (P.atom_injective i j) hab
        exact hcol.trans (congrArg some hba)
  · intro h
    rw [h]
    rfl

/-- ACTUAL one-original-E coherent local kernel intertwining at
EVERY genuine current diversity atom, including arbitrary distinct
current unary parent sorts. Original one-sort commutation and the
TWO separately guarded displayed-middle (TP) instances are
both indispensable here. -/
theorem original_coherent_current_atom_TI
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i j : B.Sorts) (a : B.source.Atom i j) :
    TRel.comp
      (originalExactCurrentKernelFamily A B P transport base hOne E i).r
      (B.source.atomRel a) =
    TRel.comp (B.source.atomRel a)
      (originalExactCurrentKernelFamily A B P transport base hOne E j).r := by
  let W := originalExactSourceKernelWords A base hOne E
  let D : RawExact.NonemptyExact A.source (P.parent i) (P.parent j) :=
    RawExact.exactDiversityAtom A.source (P.atom i j a)
  have hDword : RawExact.evaluate A.source D.words =
      A.source.atomRel (P.atom i j a) :=
    RawExact.exactDiversityAtom_relation A.source (P.atom i j a)
  have hTraceE (k : B.Sorts) (x y : B.Point k) :
      RawExact.evaluate A.source (W (P.parent k)).words
        (P.point k x) (P.point k y) ↔
      (originalExactCurrentKernelFamily A B P transport base hOne E k).r x y := by
    have hk := originalExactSourceKernelWords_relation
      A base hOne E (P.parent k)
    have hRho := PrefixExactRestriction.rho_iff
      A B P transport k
      (oldExactEqCast A.source (hOne (P.parent k)).symm E) x y
    exact (Iff.of_eq (congrFun
      (congrFun hk (P.point k x)) (P.point k y))).trans hRho.symm
  have hTraceAtom (x : B.Point i) (y : B.Point j) :
      RawExact.evaluate A.source D.words
        (P.point i x) (P.point j y) ↔
      B.source.atomRel a x y :=
    (Iff.of_eq (congrFun (congrFun hDword (P.point i x))
      (P.point j y))).trans
      (original_current_atom_old_trace A B P a x y)
  let xi : B.Point i := Classical.choice (B.source.nonemptySort i)
  let xj : B.Point j := Classical.choice (B.source.nonemptySort j)
  have hRealEi : ∃ x y : B.Point i,
      RawExact.evaluate A.source (W (P.parent i)).words
        (P.point i x) (P.point i y) := by
    refine ⟨xi,xi,?_⟩
    exact (hTraceE i xi xi).mpr
      ((originalExactCurrentKernelFamily A B P transport base hOne E i).refl xi)
  have hRealEj : ∃ x y : B.Point j,
      RawExact.evaluate A.source (W (P.parent j)).words
        (P.point j x) (P.point j y) := by
    refine ⟨xj,xj,?_⟩
    exact (hTraceE j xj xj).mpr
      ((originalExactCurrentKernelFamily A B P transport base hOne E j).refl xj)
  obtain ⟨x₀,y₀,hAtom₀⟩ := B.source.realized a
  have hRealD : ∃ x : B.Point i, ∃ y : B.Point j,
      RawExact.evaluate A.source D.words
        (P.point i x) (P.point j y) :=
    ⟨x₀,y₀,(hTraceAtom x₀ y₀).mpr hAtom₀⟩
  have hOldTI :
      TRel.comp
        (RawExact.evaluate A.source (W (P.parent i)).words)
        (RawExact.evaluate A.source D.words) =
      TRel.comp (RawExact.evaluate A.source D.words)
        (RawExact.evaluate A.source (W (P.parent j)).words) := by
    rw [hDword]
    exact (originalOneSortWordTI A base hOne E
      (RawWord.atom (P.atom i j a) (.nil (P.parent j)))).1
  funext x z
  apply propext
  calc
    TRel.comp
        (originalExactCurrentKernelFamily A B P transport base hOne E i).r
        (B.source.atomRel a) x z ↔
      (∃ y : B.Point i,
        RawExact.evaluate A.source (W (P.parent i)).words
          (P.point i x) (P.point i y) ∧
        RawExact.evaluate A.source D.words
          (P.point i y) (P.point j z)) := by
          constructor
          · rintro ⟨y,hxy,hyz⟩
            exact ⟨y,(hTraceE i x y).mpr hxy,
              (hTraceAtom y z).mpr hyz⟩
          · rintro ⟨y,hxy,hyz⟩
            exact ⟨y,(hTraceE i x y).mp hxy,
              (hTraceAtom y z).mp hyz⟩
    _ ↔ TRel.comp
        (RawExact.evaluate A.source (W (P.parent i)).words)
        (RawExact.evaluate A.source D.words)
        (P.point i x) (P.point j z) :=
          tp.product (W (P.parent i)) D hRealEi hRealD x z
    _ ↔ TRel.comp
        (RawExact.evaluate A.source D.words)
        (RawExact.evaluate A.source (W (P.parent j)).words)
        (P.point i x) (P.point j z) :=
          Iff.of_eq (congrFun (congrFun hOldTI
            (P.point i x)) (P.point j z))
    _ ↔ (∃ y : B.Point j,
        RawExact.evaluate A.source D.words
          (P.point i x) (P.point j y) ∧
        RawExact.evaluate A.source (W (P.parent j)).words
          (P.point j y) (P.point j z)) :=
          (tp.product D (W (P.parent j)) hRealD hRealEj x z).symm
    _ ↔ TRel.comp (B.source.atomRel a)
        (originalExactCurrentKernelFamily A B P transport base hOne E j).r
        x z := by
          constructor
          · rintro ⟨y,hxy,hyz⟩
            exact ⟨y,(hTraceAtom x y).mp hxy,
              (hTraceE j y z).mp hyz⟩
          · rintro ⟨y,hxy,hyz⟩
            exact ⟨y,(hTraceAtom x y).mpr hxy,
              (hTraceE j y z).mpr hyz⟩

end
end CCO.ExactEPGeometry
