import CCO.OrbitalCover.Example.PrefixSAP
import CCO.OrbitalCover.Example.CCO
import CCO.OrbitalCover.Example.Profiles

/-! Every source instance used by the bad-diagonal example is constructed
here. Triangle-definedness uses the already proved actual coordinate CCO,
then the accepted ordinary-AP triangle-fan theorem. This direction requires
no converse from a palette multiplication table or Helly property to CCO. -/
universe z
namespace CCO.OrbitalCover.Example

instance : Infinite Point := Infinite.of_injective
  (fun n : ℕ => (⟨0,0,0,0,n⟩ : Point)) (by
    intro n m h
    exact congrArg Point.n h)

theorem triangle_defined {V : Type z} (A : CompleteDiagram (S := source) V)
    (hsmall : A.SmallRealizable) : ∃ f : DiagramHom A.diagram, f.IsInjective :=
  A.triangleFullness_of_homogeneous_CCO homogeneous semanticCCO hsmall

/-- A complete one-coordinate table satisfying exactly the displayed
triangle law has a simultaneous actual block/bit realization. Singletons
and pairs require no vacuous extra triangle assumption: all palette entries
occur in the original source. -/
theorem coordinate_triangle_defined {V : Type z} [Finite V]
    (label : V → V → CoordColour) (hsym : ∀ x y, label x y = label y x)
    (htri : ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
      coordTriangle (label x y) (label y z) (label x z)) :
    ∃ block : V → ℕ, ∃ bit : V → Bit, ∀ x y, x ≠ y →
      coordinateColour (block x) (bit x) (block y) (bit y) = label x y := by
  let D : PartialDiagram source V := {
    finite_type := inferInstance
    vertexSort := fun _ => ()
    edge := fun x y _ => some (label x y,some 0)
    edge_reverse := by intro x y h a; rw [← hsym x y]; rfl }
  let A : CompleteDiagram (S := source) V := {
    diagram := D
    complete := fun x y _ => ⟨(label x y,some 0),rfl⟩ }
  have hactual : A.TrianglesRealizable := by
    intro x y z hxy hyz hxz a b c ha hb hc
    have ha' : a = (label x y,some 0) := Option.some.inj ha |>.symm
    have hb' : b = (label y z,some 0) := Option.some.inj hb |>.symm
    have hc' : c = (label x z,some 0) := Option.some.inj hc |>.symm
    subst a; subst b; subst c
    apply (triangle_iff _ _ _).mpr
    exact ⟨htri x y z hxy hyz hxz,by simp [coordTriangle]⟩
  obtain ⟨f⟩ := semanticCCO V D
    (fun C => A.cycleHom_of_AP_triangles (AtomicSource.ageAP_of_homogeneous homogeneous) hactual C)
  refine ⟨fun x => (f.point x).u, fun x => (f.point x).p, ?_⟩
  intro x y h
  have hh := f.preserves_edge x y h (label x y,some 0) rfl
  exact congrArg Prod.fst ((colour_some _ _ _).mp hh).2

/-- Complete actual nine-colour source, independent of the parity/Hasse
providers, safe splitting, and every arbitrary coarse orientation. -/
theorem actual_model :
    Nat.card Colour = 9 ∧ HomogeneousSource source Aut ∧ AgeSAP source ∧
      SemanticCCO.{0,0,z,0} source :=
  ⟨Nat.card_eq_fintype_card.trans colour_card, homogeneous, strongAmalgamation, semanticCCO⟩

namespace Prefix

def parent (c : child .both) : child .first := ⟨(), c.2.1⟩

def forgetSecond {c : child .both} (x : carrier .both c) : carrier .first (parent c) :=
  ⟨x.val, point_p .both x⟩

def forgetSecondEquiv : Sigma (carrier .both) ≃ Sigma (carrier .first) :=
  (oldEquiv .both).trans (oldEquiv .first).symm

theorem forgetSecond_literal (x : Sigma (carrier .both)) :
    forgetSecondEquiv x = ⟨parent x.1,forgetSecond x.2⟩ := by
  apply erase_injective .first
  rfl

theorem reduct_same_point (x : Sigma (carrier .both)) :
    oldEquiv .first (forgetSecondEquiv x) = oldEquiv .both x := by
  exact (oldEquiv .first).apply_symm_apply _

/-- The actual first and second named prefixes retain all three positive
properties, on literal original-point subtypes with actual occurring atoms. -/
theorem actual_prefix (k : Stage) :
    HomogeneousSource (source k) (FullGroup k) ∧ AgeSAP (source k) ∧
      SemanticCCO.{0,0,z,0} (source k) :=
  ⟨homogeneous k,strongAmalgamation k,semanticCCO k⟩

end Prefix
end CCO.OrbitalCover.Example
