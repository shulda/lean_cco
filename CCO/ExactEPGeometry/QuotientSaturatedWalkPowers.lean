import CCO.ExactEPGeometry.ProjectedOrbitalPowers

/-!
# B062 C98: equality-inclusive saturation of every quotient walk length

For an actual equivalence E, an old relation R commuting with E has
the property that a walk in the full E;R;E block can be tightened,
without changing endpoints modulo E, to one genuine R-walk of the
same length. This is the full represented-relational calculation for
the quotient parity-power formula, INCLUDING length zero (E, not Id).

The quotient pullback theorem uses only an onto class projection and
the precise fact that the quotient pivot's whole pullback equals E;R;E.
It does NOT assume quotient SAP or reverse RAW exactness, and commutation
is an explicit algebraic input here; actual source use must DISCHARGE
it from its one-sort symmetric invariant calculus.
-/

namespace CCO.ExactEPGeometry

open CCO.ParityHasse.Original

noncomputable section

/-- The literal E;R;E relation, with two genuine E-endpoint witnesses. -/
def setoidBiSaturation {X : Type*} (E : Setoid X)
    (R : X → X → Prop) : X → X → Prop :=
  fun x y => ∃ a b, E.r x a ∧ R a b ∧ E.r b y

/-- If R;E = E;R, the unwanted intermediate E zigzag in
(E;R;E);(E;R^n;E) is genuinely absorbed, giving E;R^(n+1);E.
No hypothesis on whether R is itself an equivalence is used. -/
theorem setoidBiSaturation_comp_power
    {X : Type*} (E : Setoid X) (R : X → X → Prop)
    (hComm : TRel.comp R E.r = TRel.comp E.r R)
    (n : Nat) :
    TRel.comp (setoidBiSaturation E R)
      (setoidBiSaturation E (relPow R n)) =
      setoidBiSaturation E (relPow R (n+1)) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z, ⟨a,b,hxa,hab,hbz⟩, ⟨c,d,hzc,hcd,hdy⟩⟩
    have hbc : E.r b c := E.trans hbz hzc
    have hRE : TRel.comp R E.r a c := ⟨b,hab,hbc⟩
    have hER : TRel.comp E.r R a c := by
      rw [←hComm]
      exact hRE
    obtain ⟨t,hat,htc⟩ := hER
    exact ⟨t,d,E.trans hxa hat,⟨c,htc,hcd⟩,hdy⟩
  · rintro ⟨a,b,hxa,⟨c,hac,hcb⟩,hby⟩
    exact ⟨c,⟨a,c,hxa,hac,E.refl c⟩,
      ⟨c,b,E.refl c,hcb,hby⟩⟩

/-- Every POSITIVE walk of a full E-block equals the full
E-saturation of an actual R-walk of precisely that length. -/
theorem setoidBiSaturation_positiveRelPow
    {X : Type*} (E : Setoid X) (R : X → X → Prop)
    (hComm : TRel.comp R E.r = TRel.comp E.r R)
    (n : Nat) :
    relPow (setoidBiSaturation E R) (n+1) =
      setoidBiSaturation E (relPow R (n+1)) := by
  induction n with
  | zero =>
      funext x y
      apply propext
      constructor
      · intro h
        obtain ⟨a,b,hxa,hab,hby⟩ :=
          (relPow_one (setoidBiSaturation E R) x y).mp h
        exact ⟨a,b,hxa,(relPow_one R a b).mpr hab,hby⟩
      · rintro ⟨a,b,hxa,hab,hby⟩
        apply (relPow_one (setoidBiSaturation E R) x y).mpr
        exact ⟨a,b,hxa,(relPow_one R a b).mp hab,hby⟩
  | succ n ih =>
      calc
        relPow (setoidBiSaturation E R) ((n+1)+1) =
            TRel.comp (setoidBiSaturation E R)
              (relPow (setoidBiSaturation E R) (n+1)) := rfl
        _ = TRel.comp (setoidBiSaturation E R)
              (setoidBiSaturation E (relPow R (n+1))) := by rw [ih]
        _ = setoidBiSaturation E (relPow R ((n+1)+1)) :=
          setoidBiSaturation_comp_power E R hComm (n+1)

/-- All powers, including the true quotient zero power:
pullback(Rbar^n) = E;(R^n);E, with Rbar's whole actual pullback equal
to E;R;E. We require a proved kernel equation, not a quotient section.
No symmetry or homogeneity is required in this pure algebra lemma. -/
theorem quotientRelPow_bisaturated_pullback
    {X Q : Type*} (pi : X → Q) (hsurj : Function.Surjective pi)
    (E : Setoid X) (hKernel : ∀ x y, pi x = pi y ↔ E.r x y)
    (R : X → X → Prop)
    (hComm : TRel.comp R E.r = TRel.comp E.r R)
    (D : Q → Q → Prop)
    (hPull : GroupActions.pullback pi pi D = setoidBiSaturation E R)
    (n : Nat) :
    GroupActions.pullback pi pi (relPow D n) =
      setoidBiSaturation E (relPow R n) := by
  cases n with
  | zero =>
      funext x y
      apply propext
      change (pi x = pi y) ↔
        (∃ a b, E.r x a ∧ a = b ∧ E.r b y)
      constructor
      · intro hxy
        exact ⟨x,x,E.refl x,rfl,(hKernel x y).mp hxy⟩
      · rintro ⟨a,b,hxa,hab,hby⟩
        subst b
        exact (hKernel x y).mpr (E.trans hxa hby)
  | succ n =>
      calc
        GroupActions.pullback pi pi (relPow D (n+1)) =
            relPow (GroupActions.pullback pi pi D) (n+1) :=
          quotientPullback_positiveRelPow pi hsurj D n
        _ = relPow (setoidBiSaturation E R) (n+1) := by rw [hPull]
        _ = setoidBiSaturation E (relPow R (n+1)) :=
          setoidBiSaturation_positiveRelPow E R hComm n

end
end CCO.ExactEPGeometry
