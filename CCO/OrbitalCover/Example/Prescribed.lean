import CCO.OrbitalCover.Example.Core
import CCO.OrbitalCover.Example.CoordinatePotentials

/-! The direct coordinate construction retains the literal prescribed p/q
bits of finite unary-labelled diagrams. It supplies the CCO construction for
the two chosen successive prefix expansions, without safe-splitting imports. -/
universe z
namespace CCO.OrbitalCover.Example

theorem realize_prescribed (V : Type z) (D : PartialDiagram source V)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    (P Q : Option (V → Bit))
    (hP : ∀ p, P = some p → ∀ x y (h : x ≠ y) (a : source.Atom (D.vertexSort x) (D.vertexSort y))
      (b : Bit), D.edge x y h = some a → a.1 = some b → p x+p y = b)
    (hQ : ∀ q, Q = some q → ∀ x y (h : x ≠ y) (a : source.Atom (D.vertexSort x) (D.vertexSort y))
      (b : Bit), D.edge x y h = some a → a.2 = some b → q x+q y = b) :
    ∃ f : DiagramHom D, f.IsInjective ∧
      (∀ p, P = some p → ∀ x, (f.point x).p = p x) ∧
      (∀ q, Q = some q → ∀ x, (f.point x).q = q x) := by
  classical
  have first_read {i j : Unit} (x y : Point) (a : source.Atom i j)
      (ha : source.colour x y = some a) : a.1 =
        if x.u = y.u then some (x.p+y.p) else none :=
    (congrArg Prod.fst ((colour_some x y a).mp ha).2).symm
  have second_read {i j : Unit} (x y : Point) (a : source.Atom i j)
      (ha : source.colour x y = some a) : a.2 =
        if x.v = y.v then some (x.q+y.q) else none :=
    (congrArg Prod.snd ((colour_some x y a).mp ha).2).symm
  obtain ⟨u,p,hu,hp⟩ := Potentials.coordinate_optional source D (fun a => a.1) (fun _ => rfl)
    (fun _ x => x.u) (fun _ x => x.p) (fun x y a ha => first_read x y a ha) hcycles P hP
  obtain ⟨v,q,hv,hq⟩ := Potentials.coordinate_optional source D (fun a => a.2) (fun _ => rfl)
    (fun _ x => x.v) (fun _ x => x.q) (fun x y a ha => second_read x y a ha) hcycles Q hQ
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
  refine ⟨f,?_,?_,?_⟩
  · intro x y he
    exact hcode (congrArg (fun z : Sigma (fun _ : Unit => Point) => z.2.n) he)
  · intro fixed he x
    exact congrFun (hp fixed he) x
  · intro fixed he x
    exact congrFun (hq fixed he) x

end CCO.OrbitalCover.Example
