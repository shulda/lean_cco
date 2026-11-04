import CCO.UnaryTermsReturn.CommonBlockModel
import CCO.RealClosure.Bounds.Examples.CycleConsistency

/-!
# B052 source10 C16: actual old semantic CCO of the two-sort block model

The genuine original two-sorted common-block structure has one Boolean
old diversity atom indicating equality of block labels. Every cycle
consistency test enforces one compatible block label, by the accepted
generic CycleConsistency.coordinate_labels theorem.

Different formal vertices receive injectively distinct REAL clone codes;
this preserves same-block same-sort diversity and never replaces it by
logical old equality. There is no old SAP, hidden SAP, or quotient
homogeneity premise.
-/

universe z
namespace CCO.UnaryTermsReturn

/-- The old typed Boolean atom records equality of original
block labels, not real point equality. -/
def commonBlockEqReader :
    RealClosure.Bounds.Examples.CycleConsistency.Reader
      commonBlockOriginalAtomicSource :=
  fun {_ _} a => a

theorem commonBlockEqReader_value
    {i j : Bool} (x : CommonBlockReal i)
    (y : CommonBlockReal j) (a : Bool)
    (ha : commonBlockOriginalAtomicSource.colour x y = some a) :
    (x.1 = y.1 ↔ a = true) := by
  change commonBlockOldColour i j x y = some a at ha
  have hTaggedNe : (⟨i,x⟩ : Sigma CommonBlockReal) ≠ ⟨j,y⟩ := by
    intro hTagged
    have hn : commonBlockOldColour i j x y = none := by
      simp only [commonBlockOldColour, if_pos hTagged]
    rw [hn] at ha
    cases ha
  have hDecide : decide (x.1 = y.1) = a := by
    simpa only [commonBlockOldColour, if_neg hTaggedNe,
      Option.some.injEq] using ha
  constructor
  · intro hxy
    exact hDecide.symm.trans (decide_eq_true_eq.mpr hxy)
  · intro hTrue
    exact decide_eq_true_eq.mp (hDecide.trans hTrue)

/-- True original CCO for the concrete two-sorted common-block
atomic source. Every finite partial diagram whose actual specified
simple cycles are realizable has an actual old homomorphism.
The two old sorts and all diversity colours are preserved.
Independent fresh clone codes prevent a false diagonal collapse. -/
theorem commonBlockOriginalSemanticCCO :
    SemanticCCO.{0,0,z,0} commonBlockOriginalAtomicSource := by
  intro V D hcycles
  let S := commonBlockOriginalAtomicSource
  have hSym :
      ∀ {i j : Bool} (a : S.Atom i j),
        commonBlockEqReader (S.conv a) = commonBlockEqReader a := by
    intro i j a
    rfl
  obtain ⟨label,hLabel⟩ :=
    RealClosure.Bounds.Examples.CycleConsistency.coordinate_labels
      S D commonBlockEqReader hSym
      (fun _ (x : CommonBlockReal _) => x.1)
      (fun x y a ha => commonBlockEqReader_value x y a ha)
      hcycles
  classical
  letI : Finite V := D.finite_type
  letI : Fintype V := Fintype.ofFinite V
  let code : V → ℕ := fun x => ((Fintype.equivFin V) x).val
  have hCodeInj : Function.Injective code := by
    intro x y hxy
    apply (Fintype.equivFin V).injective
    exact Fin.ext hxy
  refine ⟨{
    point := fun x => (label x,code x)
    preserves_edge := ?_
  }⟩
  intro x y hxy a ha
  have hRead : label x = label y ↔ a = true := by
    exact hLabel x y hxy a ha
  have hBool : decide (label x = label y) = a := by
    cases a with
    | false =>
        have hne : label x ≠ label y := by
          intro heq
          have hFalse : false = true := hRead.mp heq
          cases hFalse
        simp [hne]
    | true =>
        have heq : label x = label y := hRead.mpr rfl
        exact decide_eq_true_eq.mpr heq
  have hTaggedNe :
      (⟨D.vertexSort x,(label x,code x)⟩ : Sigma CommonBlockReal) ≠
        ⟨D.vertexSort y,(label y,code y)⟩ := by
    intro heq
    have hCodes : code x = code y :=
      congrArg (fun p : Sigma CommonBlockReal => p.2.2) heq
    exact hxy (hCodeInj hCodes)
  change commonBlockOldColour
    (D.vertexSort x) (D.vertexSort y)
    (label x,code x) (label y,code y) = some a
  unfold commonBlockOldColour
  rw [if_neg hTaggedNe]
  exact congrArg Option.some hBool

end CCO.UnaryTermsReturn
