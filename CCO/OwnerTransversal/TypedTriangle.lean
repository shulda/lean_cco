import CCO.OwnerTransversal.TypedPalette
import CCO.OwnerTransversal.AnchoredCaps
import CCO.RawExact.QuotientTriangleFullness

/-! The original source triangle-fullness instance is kept separate
from owner completion and from the residual transversal hypotheses. -/
universe v w t
namespace CCO.OwnerTransversal
open ParityHasse.Original RawExact FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

def RawRecords.TrianglesLegal {V : Type} (D : RawRecords S V) : Prop :=
  ∀ x y z, ∃ a b c : M,
    S.colour (i := ()) (j := ()) a b = D.edge x y ∧
    S.colour (i := ()) (j := ()) a c = D.edge x z ∧
    S.colour (i := ()) (j := ()) b c = D.edge y z

include H in
/-- Original identity-kernel specialization of the accepted actual
quotient triangle theorem. Repeated-index boundary cases are retained. -/
theorem raw_triangle_fullness {V : Type} [Finite V]
    (cco : SemanticCCO.{0,v,0,w} S) (D : RawRecords S V)
    (complete : ∀ x y, x ≠ y → ∃ a, D.edge x y = some a)
    (hTriangles : RawRecords.TrianglesLegal S D) :
    ∃ f : V → M, RawRecords.Hom S D f ∧ Function.Injective f := by
  classical
  let Q : Unit → Type v := fun _ => M
  let d : ActualOrbitalDiagram G Q V := {
    sort := fun _ => ()
    relation := fun x y a b => S.colour (i := ()) (j := ()) a b = D.edge x y
    actual := by
      intro x y
      cases hc : D.edge x y with
      | none =>
        obtain ⟨a⟩ := S.nonemptySort ()
        refine ⟨a,a,?_⟩
        funext u v
        apply propext
        rw [old_orbital_iff_colour S H]
        exact Iff.of_eq (congrArg (fun col => S.colour (i := ()) (j := ()) u v = col)
          ((S.colour_none_iff a a).mpr rfl).symm)
      | some c =>
        obtain ⟨a,b,hab⟩ := S.realized c
        refine ⟨a,b,?_⟩
        funext u v
        apply propext
        rw [old_orbital_iff_colour S H]
        simp only [RealHull.Geometry.col,hab]
    reverse := by intro x y a b; rw [colour_symmetric S a b,D.symmetric]
    diagonal := by
      intro x a b
      rw [D.diagonal]
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using
        S.colour_none_iff (i := ()) (j := ()) a b
    separates := by
      intro x y hxy a b hab
      obtain ⟨c,hc⟩ := complete x y hxy
      exact S.atomRel_ne (hab.trans hc) }
  obtain ⟨point,hpoint,hinj⟩ := actual_quotient_triangle_fullness_of_CCO S H
    (semanticCCO_change_universe S cco) Q (fun _ => ()) (fun _ => id)
    (fun _ => Function.surjective_id) (fun _ _ _ => rfl)
    (fun _ => exactIdentityAtom S ())
    (fun _ => by rw [exactIdentityAtom_relation]; rfl) d hTriangles
  refine ⟨point,?_,?_⟩
  · intro x y a ha
    exact (hpoint x y).trans ha
  · intro x y hxy
    apply hinj
    exact congrArg (Sigma.mk ()) hxy

end CCO.OwnerTransversal
