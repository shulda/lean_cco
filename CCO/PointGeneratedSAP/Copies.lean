import CCO.PointGeneratedSAP.Alignment
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card

/-! Actual repeated strong copies over ONE fixed full point-generated base.
Only real homogeneity and SAP enter; PGO and avoidance do not occur. -/
universe u v w
namespace CCO.PointGeneratedSAP
open UnaryFreshFrames
variable {L : Language.{u}} {V : Type v} {H : Structure L V}
variable {O : Original L V H} (C : Interpretation H O)
namespace Interpretation
include C

/-- Every finite set has a finite point-generated cover, choosing actual
single real sources. Extra cover vertices are retained, not discarded. -/
theorem finite_cover (F : Set V) (hF : F.Finite) :
    ∃ P : Piece O, F ⊆ P.points := by
  classical
  let rep : V → O.Real := fun x => (C.generating x).choose
  let D := rep '' F
  let P := Piece.ofReal C D (hF.image rep)
  refine ⟨P,?_⟩
  intro x hx
  have ht := (C.generating x).choose_spec
  apply H.closure_mono (B := Subtype.val '' D) _ ht
  intro y hy
  have he : y = (rep x).val := hy
  exact ⟨rep x,⟨x,hx,rfl⟩,he.symm⟩

/-- A whole factor can be moved by ONE ORIGINAL automorphism, fixing its
full base. This consequence uses SAP alone, without any orbit premise. -/
def FreshMotion : Prop :=
  ∀ (A B D : Piece O), A.points ⊆ B.points → A.points ⊆ D.points →
    ∃ g : O.Aut, (∀ a ∈ A.points, C.lift g • a = a) ∧
      ∀ b ∈ B.points, ∀ d ∈ D.points, C.lift g • d = b → d ∈ A.points

theorem freshMotion_of_ageSAP (hom : O.Homogeneous) (sap : AgeSAP O) : C.FreshMotion := by
  intro A B D hAB hAD
  let s : A.Embedding B.points := Structure.Piece.Embedding.inclusion hAB
  let t : A.Embedding D.points := Structure.Piece.Embedding.inclusion hAD
  obtain ⟨F,l,r,agree,strong⟩ := sap A B D s t
  obtain ⟨a,ha⟩ := align C hom B l.ambient (Structure.Piece.Embedding.identity B.toPiece).ambient
  let q : D.Embedding Set.univ := (r.mapAut (C.lift a)).ambient
  obtain ⟨g,hg⟩ := align C hom D (Structure.Piece.Embedding.identity D.toPiece).ambient q
  have hq (d : D.points) : C.lift g • d.val = C.lift a • r.point d := hg d
  have hl (b : B.points) : C.lift a • l.point b = b.val := ha b
  refine ⟨g,?_,?_⟩
  · intro x hx
    have he := agree ⟨x,hx⟩
    change l.point ⟨x,hAB hx⟩ = r.point ⟨x,hAD hx⟩ at he
    exact (hq ⟨x,hAD hx⟩).trans
      ((congrArg (fun z => C.lift a • z) he.symm).trans (hl ⟨x,hAB hx⟩))
  · intro b hb d hd hmove
    have he : l.point ⟨b,hb⟩ = r.point ⟨d,hd⟩ := by
      apply MulAction.injective (C.lift a)
      exact (hl ⟨b,hb⟩).trans (hmove.symm.trans (hq ⟨d,hd⟩))
    obtain ⟨x,_,hx⟩ := strong ⟨b,hb⟩ ⟨d,hd⟩ he
    change x.val = d at hx
    exact hx ▸ x.property

/-- One fresh copy avoids the ENTIRE existing finite family. -/
theorem freshMotion_avoids_family (fresh : C.FreshMotion) (A B : Piece O)
    (hAB : A.points ⊆ B.points) {ι : Type w} [Finite ι] (f : ι → O.Aut) :
    ∃ g : O.Aut, (∀ a ∈ A.points, C.lift g • a = a) ∧
      ∀ i, ∀ x ∈ B.points, ∀ y ∈ B.points,
        C.lift g • x = C.lift (f i) • y → x ∈ A.points := by
  let U := A.points ∪ ⋃ i, (fun x => C.lift (f i) • x) '' B.points
  have hu : U.Finite := A.finite.union (Set.finite_iUnion fun _ => B.finite.image _)
  obtain ⟨F,hF⟩ := C.finite_cover U hu
  obtain ⟨g,hfix,havoid⟩ := fresh A F B (fun x hx => hF (Or.inl hx)) hAB
  refine ⟨g,hfix,?_⟩
  intro i x hx y hy he
  exact havoid (C.lift (f i) • y)
    (hF (Or.inr (Set.mem_iUnion.mpr ⟨i,y,hy,rfl⟩))) x hx he

/-- C14: n same-base copies, with every previous pairwise intersection
preserved. These are actual original automorphisms and induced copies. -/
theorem exists_same_base_automorphisms (fresh : C.FreshMotion) (A B : Piece O)
    (hAB : A.points ⊆ B.points) (n : ℕ) :
    ∃ f : Fin n → O.Aut,
      (∀ i, ∀ a ∈ A.points, C.lift (f i) • a = a) ∧
      ∀ i j, i ≠ j → ∀ x ∈ B.points, ∀ y ∈ B.points,
        C.lift (f i) • x = C.lift (f j) • y → x ∈ A.points := by
  induction n with
  | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨f,hfix,hinter⟩ := ih
    obtain ⟨g,hgfix,hgavoid⟩ := C.freshMotion_avoids_family fresh A B hAB f
    refine ⟨Fin.cases g f,?_,?_⟩
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
          have heq : x = y := MulAction.injective (C.lift (f i))
            (he.trans ((hgfix y hyA).trans (hfix i y hyA).symm))
          exact heq ▸ hyA
        | succ j => exact hinter i j (fun hij => hne (congrArg Fin.succ hij)) x hx y hy he

/-- The finite point-generated host contains n genuinely induced copies.
They agree on the same literal full base and meet nowhere else. -/
theorem exists_many_strong_copies (hom : O.Homogeneous) (sap : AgeSAP O)
    (A B : Piece O) (hAB : A.points ⊆ B.points) (n : ℕ) :
    ∃ (F : Piece O) (f : Fin n → B.Embedding F.points),
      (∀ i a (ha : a ∈ A.points), (f i).point ⟨a,hAB ha⟩ = a) ∧
      ∀ i j, i ≠ j → ∀ x y, (f i).point x = (f j).point y →
        x.val ∈ A.points ∧ x.val = y.val := by
  obtain ⟨g,hfix,hinter⟩ := C.exists_same_base_automorphisms
    (C.freshMotion_of_ageSAP hom sap) A B hAB n
  let U := A.points ∪ ⋃ i, (fun x => C.lift (g i) • x) '' B.points
  obtain ⟨F,hF⟩ := C.finite_cover U
    (A.finite.union (Set.finite_iUnion fun _ => B.finite.image _))
  let f (i : Fin n) : B.Embedding F.points :=
    ((Structure.Piece.Embedding.identity B.toPiece).mapAut (C.lift (g i))).restrictTarget
      (fun x => hF (Or.inr (Set.mem_iUnion.mpr ⟨i,x.val,x.property,rfl⟩)))
  refine ⟨F,f,hfix,?_⟩
  intro i j hne x y he
  have hxA : x.val ∈ A.points := hinter i j hne x.val x.property y.val y.property he
  have hval : x.val = C.lift (g j) • y.val := (hfix i x.val hxA).symm.trans he
  have hyval : y.val = x.val := MulAction.injective (C.lift (g j))
    (hval.symm.trans (hfix j x.val hxA).symm)
  exact ⟨hxA,hyval.symm⟩

end Interpretation
end CCO.PointGeneratedSAP
