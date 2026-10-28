import CCO.RealHull.Geometry.RamseySource

/-! Literal old-colour Ramsey on arbitrary subsets. FINITENESS precedes every
natural-cardinality inequality, including empty diversity palettes. -/
universe v w
namespace CCO.RealHull.Canonical
open Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

theorem looped_colour_of_embedding (e : Fin (sourceTriangleRamsey S) ↪ M) :
    ∃ a : Atom S, Looped S a ∧ ∃ i j, i ≠ j ∧ col S (e i) (e j) = some a := by
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
  exact ⟨a,(mem_row S a a a).mpr ⟨e x,e y,e z,ha,hc,hb⟩,x,y,hxy,ha⟩


theorem finite_subset_of_no_looped (Z : Set M)
    (hloop : ∀ a : Atom S, (∃ x y : Z, col S x.val y.val = some a) → ¬ Looped S a) :
    Finite Z ∧ Nat.card Z < sourceTriangleRamsey S := by
  apply TriangleRamsey.finite_card_lt_of_no_embedding
  rintro ⟨e⟩
  let em : Fin (sourceTriangleRamsey S) ↪ M := ⟨fun i => (e i).val,
    fun i j he => e.injective (Subtype.ext he)⟩
  obtain ⟨a,ha,i,j,_,hij⟩ := looped_colour_of_embedding S em
  exact hloop a ⟨e i,e j,hij⟩ ha

end CCO.RealHull.Canonical
