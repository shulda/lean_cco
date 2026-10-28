import CCO.RealHull.Geometry.Algebra
import CCO.RealHull.Geometry.TriangleRamsey

/-! A source consumer of the finite triangle Ramsey proof. The no-injection
bound forces FINITENESS before stating a natural-cardinality inequality. -/
universe v w
namespace CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

noncomputable def paletteColourCount : Nat := max 1 (Nat.card (Atom S))
theorem paletteColourCount_pos : 0 < paletteColourCount S :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

noncomputable def sourceTriangleRamsey : Nat :=
  TriangleRamsey.ramseyNumber (paletteColourCount S) (paletteColourCount_pos S)

def Looped (a : Atom S) : Prop := a ∈ square S a

theorem no_looped_no_embedding (hloop : ∀ a : Atom S, ¬ Looped S a) :
    ¬ Nonempty (Fin (sourceTriangleRamsey S) ↪ M) := by
  classical
  letI : Fintype (Atom S) := S.finiteAtom () ()
  let k := paletteColourCount S
  have hk : 0 < k := paletteColourCount_pos S
  have hcard : Fintype.card (Atom S) ≤ k := by
    simpa only [k,paletteColourCount,Nat.card_eq_fintype_card] using
      (Nat.le_max_right 1 (Fintype.card (Atom S)))
  let code : Atom S → Fin k := fun a =>
    ⟨(Fintype.equivFin (Atom S) a).val,Nat.lt_of_lt_of_le (Fintype.equivFin (Atom S) a).isLt hcard⟩
  have code_inj : Function.Injective code := by
    intro a b he
    apply (Fintype.equivFin (Atom S)).injective
    exact Fin.ext (congrArg (fun z : Fin k => z.val) he)
  rintro ⟨e⟩
  let read : FullColour S → Fin k := fun c => match c with
    | none => ⟨0,hk⟩
    | some a => code a
  let colour : Fin (sourceTriangleRamsey S) → Fin (sourceTriangleRamsey S) → Fin k :=
    fun x y => read (col S (e x) (e y))
  have hsym : ∀ x y, colour x y = colour y x := by
    intro x y
    exact congrArg read (col_symm S (e x) (e y))
  obtain ⟨x,y,z,hxy,hyz,hxz,hcol1,hcol2⟩ :=
    TriangleRamsey.ramseyNumber_spec k hk colour hsym
  obtain ⟨a,ha⟩ := col_some_of_ne S (e.injective.ne hxy)
  obtain ⟨b,hb⟩ := col_some_of_ne S (e.injective.ne hxz)
  obtain ⟨c,hc⟩ := col_some_of_ne S (e.injective.ne hyz)
  have hab : a = b := code_inj (by simpa only [colour,read,ha,hb] using hcol1)
  have hac : a = c := code_inj (by simpa only [colour,read,ha,hc] using hcol2)
  subst b
  subst c
  exact hloop a ((mem_row S a a a).mpr ⟨e x,e y,e z,ha,hc,hb⟩)

theorem finite_source_of_no_looped (hloop : ∀ a : Atom S, ¬ Looped S a) :
    Finite M ∧ Nat.card M < sourceTriangleRamsey S :=
  TriangleRamsey.finite_card_lt_of_no_embedding _ (no_looped_no_embedding S hloop)

end CCO.RealHull.Geometry
