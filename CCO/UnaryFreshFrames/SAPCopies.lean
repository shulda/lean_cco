import CCO.UnaryFreshFrames.SAPAlgebraicity

/-! C08–C10: actual arbitrarily many induced copies over ONE fixed base.
All copies and their full finite induced host are constructed inside H;
extra host points are harmless, and no real generators are required. -/
universe u v w
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

namespace Piece
variable {H} {ι : Type w} [Finite ι]

/-- The actual induced host of a finite family of entire closed images. -/
def familyHost (A B : H.Piece) (g : ι → H.Aut) : H.Piece where
  points := A.points ∪ ⋃ i, (fun x => g i • x) '' B.points
  finite := A.finite.union (Set.finite_iUnion fun i => B.finite.image _)
  closed := by
    rintro F x (hx | hx)
    · exact Or.inl (A.closed F x hx)
    · obtain ⟨i, y, hy, he⟩ := Set.mem_iUnion.mp hx
      subst x
      exact Or.inr (Set.mem_iUnion.mpr
        ⟨i, H.func F y, B.closed F y hy, H.aut_func (g i) F y⟩)

end Piece

/-- One extra whole closed copy avoids ALL members of a finite family,
using a SINGLE fresh motion over the same actual closed base. -/
theorem freshMotion_avoids_family (fresh : H.FreshMotion) (A B : H.Piece)
    (hAB : A.points ⊆ B.points) {ι : Type w} [Finite ι] (f : ι → H.Aut) :
    ∃ g : H.Aut, (∀ a ∈ A.points, g • a = a) ∧
      ∀ i, ∀ x ∈ B.points, ∀ y ∈ B.points, g • x = f i • y → x ∈ A.points := by
  obtain ⟨g, hfix, havoid⟩ := fresh A (A.familyHost B f) B (fun _ ha => Or.inl ha) hAB
  refine ⟨g, hfix, ?_⟩
  intro i x hx y hy he
  exact havoid (f i • y) (Or.inr (Set.mem_iUnion.mpr ⟨i, y, hy, rfl⟩)) x hx he

/-- The literal list of n aligned copies. Distinct copies intersect only
in their fixed base; a possibly empty off-base part causes no exception. -/
theorem exists_same_base_automorphisms (fresh : H.FreshMotion) (A B : H.Piece)
    (hAB : A.points ⊆ B.points) (n : ℕ) :
    ∃ f : Fin n → H.Aut,
      (∀ i, ∀ a ∈ A.points, f i • a = a) ∧
      ∀ i j, i ≠ j → ∀ x ∈ B.points, ∀ y ∈ B.points,
        f i • x = f j • y → x ∈ A.points := by
  induction n with
  | zero =>
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨f, hfix, hinter⟩ := ih
    obtain ⟨g, hgfix, hgavoid⟩ := H.freshMotion_avoids_family fresh A B hAB f
    refine ⟨Fin.cases g f, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact hgfix
      | succ i => exact hfix i
    · intro i j hne x hx y hy he
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact False.elim (hne rfl)
        | succ j => exact hgavoid j x hx y hy he
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          have hyA : y ∈ A.points := hgavoid i y hy x hx he.symm
          have heq : x = y := MulAction.injective (f i)
            (he.trans ((hgfix y hyA).trans (hfix i y hyA).symm))
          exact heq ▸ hyA
        | succ j =>
          exact hinter i j (fun hij => hne (congrArg Fin.succ hij)) x hx y hy he

/-- Actual n-copy strong amalgam host for C08, with induced full maps and
literal common A. The entire finite host is unary-closed inside H. -/
theorem exists_many_strong_copies (hom : H.Homogeneous) (sap : H.AgeSAP)
    (A B : H.Piece) (hAB : A.points ⊆ B.points) (n : ℕ) :
    ∃ (D : H.Piece) (f : Fin n → B.Embedding D.points),
      (∀ i a (ha : a ∈ A.points), (f i).point ⟨a, hAB ha⟩ = a) ∧
      ∀ i j, i ≠ j → ∀ x y, (f i).point x = (f j).point y →
        x.val ∈ A.points ∧ x.val = y.val := by
  obtain ⟨g, hfix, hinter⟩ := H.exists_same_base_automorphisms
    (H.freshMotion_of_ageSAP hom sap) A B hAB n
  let D := A.familyHost B g
  let f (i : Fin n) : B.Embedding D.points :=
    ((Piece.Embedding.identity B).mapAut (g i)).restrictTarget
      (fun x => Or.inr (Set.mem_iUnion.mpr ⟨i, x.val, x.property, rfl⟩))
  refine ⟨D, f, hfix, ?_⟩
  intro i j hne x y he
  have hxA : x.val ∈ A.points := hinter i j hne x.val x.property y.val y.property he
  have hval : x.val = g j • y.val := (hfix i x.val hxA).symm.trans he
  have hyval : y.val = x.val := MulAction.injective (g j)
    (hval.symm.trans (hfix j x.val hxA).symm)
  exact ⟨hxA, hyval.symm⟩

/-- C10's explicit unbounded-cardinality witness: the same-base copies
produce n DISTINCT points in the actual full-Aut stabilizer orbit. -/
theorem exists_many_distinct_orbit_points (hom : H.Homogeneous) (sap : H.AgeSAP)
    (A B : H.Piece) (hAB : A.points ⊆ B.points) (x : V)
    (hx : x ∈ B.points) (hnot : x ∉ A.points) (n : ℕ) :
    ∃ f : Fin n → V, Function.Injective f ∧
      ∀ i, f i ∈ orbitOver H.Aut A.points x := by
  obtain ⟨g, hfix, hinter⟩ := H.exists_same_base_automorphisms
    (H.freshMotion_of_ageSAP hom sap) A B hAB n
  refine ⟨fun i => g i • x, ?_, ?_⟩
  · intro i j he
    by_contra hne
    exact hnot (hinter i j hne x hx x hx he)
  · intro i
    exact (mem_orbitOver_iff H.Aut).mpr ⟨g i, hfix i, rfl⟩

end CCO.UnaryFreshFrames.Structure
