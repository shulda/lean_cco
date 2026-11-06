import CCO.TypedRelation

/-!
# B062 C109: a necessary nonempty-input hypothesis in actual trace products

The source trace-product theorem requires BOTH input traces to be
nonempty. The following literal two-point OLD carrier with three
unary trace blocks gives a precise counterexample if the left input
trace is empty: D is old logical identity, E is the whole old
relation; u and z select false, whereas v selects true.

No generated "equality diversity atom", false SAP premise, or
changed source result is involved. This proves only the required
boundary example; it does not alter the true trace-product theorem.
-/

namespace CCO.ExactEPGeometry

private def singletonTrace (R : Bool → Bool → Prop)
    (P Q : Bool → Prop) : Bool → Bool → Prop :=
  fun x y => P x ∧ Q y ∧ R x y

private def u : Bool → Prop := fun x => x = false
private def v : Bool → Prop := fun x => x = true
private def z : Bool → Prop := fun x => x = false

private def D : Bool → Bool → Prop := fun x y => x = y
private def E : Bool → Bool → Prop := fun _ _ => True

/-- The actual equality-inclusive TRel family on the one real Bool sort. -/
private abbrev boolCarrier : Unit → Type := fun _ => Bool

/-- A fully typed old relational product; specifying the actual sole
sort prevents Lean from guessing independent implicit sort families. -/
private def typedBoolComp (R S : Bool → Bool → Prop) : Bool → Bool → Prop :=
  TRel.comp (X := boolCarrier) (i := ()) (j := ()) (k := ()) R S

private def typedBoolNonempty (R : Bool → Bool → Prop) : Prop :=
  TRel.Nonempty (X := boolCarrier) (i := ()) (j := ()) R

/-- The first OLD input trace D|u×v is genuinely empty, even though
the second E|v×z is realized and the full old D;E reaches u×z. -/
theorem originalC109_firstInputTrace_empty :
    ¬ typedBoolNonempty (singletonTrace D u v) := by
  rintro ⟨x,y,hx,hy,hxy⟩
  have hBad : false = true := by
    calc
      false = x := hx.symm
      _ = y := hxy
      _ = true := hy
  exact (by decide : false ≠ true) hBad

/-- The LHS trace-first product cannot reach the point (false,false)
because any intermediate v point is true, while D requires equality. -/
theorem originalC109_traceFirst_false :
    ¬ typedBoolComp (singletonTrace D u v)
        (singletonTrace E v z) false false := by
  rintro ⟨y,hy,_⟩
  have hBad : false = true := hy.2.2.trans hy.2.1
  exact (by decide : false ≠ true) hBad

/-- The full old product D;E DOES contain the real (false,false)
pair, since its intermediate witness can be the old point false. -/
theorem originalC109_fullProduct_true :
    singletonTrace (typedBoolComp D E) u z false false := by
  refine ⟨rfl,rfl,?_⟩
  exact ⟨false,rfl,trivial⟩

/-- C109: dropping nonemptiness of either input trace from the
source (TP) theorem is invalid. Here the first input trace is empty
but the full old product has nonempty u×z trace. -/
theorem originalC109_nonemptyInput_guard_necessary :
    typedBoolComp (singletonTrace D u v)
      (singletonTrace E v z) ≠
    singletonTrace (typedBoolComp D E) u z := by
  intro h
  apply originalC109_traceFirst_false
  rw [h]
  exact originalC109_fullProduct_true


/-- The dual boundary has a genuinely empty SECOND input trace:
the old identity relation cannot connect true in v to false in z. -/
theorem originalC109_secondInputTrace_empty :
    ¬ typedBoolNonempty (singletonTrace D v z) := by
  rintro ⟨x,y,hx,hy,hxy⟩
  have hBad : true = false := by
    calc
      true = x := hx.symm
      _ = y := hxy
      _ = false := hy
  exact (by decide : true ≠ false) hBad

/-- The dual composition Top;Id provides the second failure: the first
trace is realized, but the second is empty, so its product is empty. -/
theorem originalC109_secondTraceFirst_false :
    ¬ typedBoolComp (singletonTrace E u v)
        (singletonTrace D v z) false false := by
  rintro ⟨m,_,hm⟩
  have hBad : true = false := hm.1.symm.trans hm.2.2
  exact (by decide : true ≠ false) hBad

/-- The FULL old Top;Id product is still nonempty on u×z. -/
theorem originalC109_secondFullProduct_true :
    singletonTrace (typedBoolComp E D) u z false false := by
  refine ⟨rfl,rfl,?_⟩
  exact ⟨false,trivial,rfl⟩

/-- The second nonempty-input hypothesis also cannot be removed,
independently of the first-input boundary. -/
theorem originalC109_secondInput_guard_necessary :
    typedBoolComp (singletonTrace E u v)
      (singletonTrace D v z) ≠
    singletonTrace (typedBoolComp E D) u z := by
  intro h
  apply originalC109_secondTraceFirst_false
  rw [h]
  exact originalC109_secondFullProduct_true

end CCO.ExactEPGeometry
