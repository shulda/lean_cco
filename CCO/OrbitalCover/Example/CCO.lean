import CCO.OrbitalCover.Example.Core
import CCO.OrbitalCover.Example.CoordinatePotentials

/-! Direct semantic HOM CCO: the two optional signed coordinates are solved
independently from actual specified simple cycles, then fresh clone indices
separate every formal vertex. This proof uses no profile/Helly converse. -/
universe z
namespace CCO.OrbitalCover.Example

private theorem first_read {i j : Unit} (x y : Point) (a : source.Atom i j)
    (ha : source.colour x y = some a) : a.1 =
      if x.u = y.u then some (x.p+y.p) else none :=
  (congrArg Prod.fst ((colour_some x y a).mp ha).2).symm

private theorem second_read {i j : Unit} (x y : Point) (a : source.Atom i j)
    (ha : source.colour x y = some a) : a.2 =
      if x.v = y.v then some (x.q+y.q) else none :=
  (congrArg Prod.snd ((colour_some x y a).mp ha).2).symm

/-- The actual infinite nine-colour product has semantic homomorphic CCO,
for partial diagrams in any finite vertex universe. The produced realization
can in fact be chosen injective by its clone indices. -/
theorem semanticCCO_injective (V : Type z) (D : PartialDiagram source V)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ f : DiagramHom D, f.IsInjective := by
  classical
  obtain ⟨u,p,hu⟩ := Potentials.coordinate_solution source D (fun a => a.1) (fun _ => rfl)
    (fun _ x => x.u) (fun _ x => x.p) (fun x y a ha => first_read x y a ha) hcycles
  obtain ⟨v,q,hv⟩ := Potentials.coordinate_solution source D (fun a => a.2) (fun _ => rfl)
    (fun _ x => x.v) (fun _ x => x.q) (fun x y a ha => second_read x y a ha) hcycles
  letI : Finite V := D.finite_type
  letI : Fintype V := Fintype.ofFinite _
  let code : V → ℕ := fun x => (Fintype.equivFin V x).val
  have hcode : Function.Injective code := Fin.val_injective.comp (Fintype.equivFin V).injective
  let f : DiagramHom D := {
    point := fun x => ⟨u x,v x,p x,q x,code x⟩
    preserves_edge := by
      intro x y h a ha
      apply (colour_some _ _ a).mpr
      constructor
      · intro he
        exact h (hcode (congrArg Point.n he))
      · exact Prod.ext (hu x y h a ha).symm (hv x y h a ha).symm
  }
  refine ⟨f,?_⟩
  intro x y he
  exact hcode (congrArg (fun z : Sigma (fun _ : Unit => Point) => z.2.n) he)

theorem semanticCCO : SemanticCCO.{0,0,z,0} source := by
  intro V D hcycles
  exact ⟨(semanticCCO_injective V D hcycles).choose⟩

end CCO.OrbitalCover.Example
