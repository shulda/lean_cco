import CCO.OrbitalCover.Example.Core
import CCO.ParityHasse.Original.RelativeIndices
import Mathlib.Tactic.FinCases

/-! The full diagonal two-cover and arbitrary orientations. All relations
include logical equality; the clone diversity colour remains irreflexive. -/
namespace CCO.OrbitalCover.Example
open ParityHasse.Original
open scoped CharTwo

def blockKey (x : Point) := (x.u,x.v)
def diagonalKey (x : Point) := (blockKey x,x.p+x.q)
def ownerKey (x : Point) := (blockKey x,x.p,x.q)
def coarseSetoid : Setoid Point := Setoid.ker blockKey
def diagonalSetoid : Setoid Point := Setoid.ker diagonalKey
def ownerSetoid : Setoid Point := Setoid.ker ownerKey

@[simp] theorem coarse_iff (x y : Point) :
    coarseSetoid x y ↔ x.u=y.u ∧ x.v=y.v := by
  change blockKey x=blockKey y ↔ _
  simp [blockKey]

@[simp] theorem diagonal_iff (x y : Point) :
    diagonalSetoid x y ↔ x.u=y.u ∧ x.v=y.v ∧ x.p+x.q=y.p+y.q := by
  change diagonalKey x=diagonalKey y ↔ _
  simp [diagonalKey,blockKey,and_assoc]

@[simp] theorem owner_iff (x y : Point) :
    ownerSetoid x y ↔ x.u=y.u ∧ x.v=y.v ∧ x.p=y.p ∧ x.q=y.q := by
  change ownerKey x=ownerKey y ↔ _
  simp [ownerKey,blockKey,and_assoc]

theorem bit_cross (a b c d : Bit) : a+b=c+d ↔ a+c=b+d := by
  have go (a b c d : Bit) (h : a+b=c+d) : a+c=b+d := by
    have h0 : (a+b)+(c+d)=0 := by rw [h]; simp
    apply CharTwo.add_eq_zero.mp
    convert h0 using 1 <;> ac_rfl
  exact ⟨go a b c d,go a c b d⟩

theorem coarse_pattern (x y : Point) :
    coarseSetoid x y ↔ (pattern x y).1.isSome=true ∧
      (pattern x y).2.isSome=true := by
  simp [pattern]

theorem diagonal_pattern (x y : Point) :
    diagonalSetoid x y ↔ ∃ b : Bit, pattern x y=(some b,some b) := by
  simp only [diagonal_iff,pattern,Prod.mk.injEq,coordinateColour_some]
  constructor
  · rintro ⟨hu,hv,hpq⟩
    exact ⟨x.p+y.p,⟨hu,rfl⟩,hv,(bit_cross x.p x.q y.p y.q).mp hpq |>.symm⟩
  · rintro ⟨b,⟨hu,hp⟩,hv,hq⟩
    exact ⟨hu,hv,(bit_cross x.p x.q y.p y.q).mpr (hp.trans hq.symm)⟩

def coarse : ColourEq source () := ⟨coarseSetoid,by
  intro x y x' y' h
  rw [coarse_pattern,coarse_pattern,pattern_of_colour h]⟩

def diagonal : ColourEq source () := ⟨diagonalSetoid,by
  intro x y x' y' h
  rw [diagonal_pattern,diagonal_pattern,pattern_of_colour h]⟩

theorem diagonal_le_coarse : diagonal ≤ coarse := by
  intro x y h
  apply (coarse_iff x y).mpr
  exact ⟨((diagonal_iff x y).mp h).1,((diagonal_iff x y).mp h).2.1⟩

theorem bit_cases (b : Bit) : b=0 ∨ b=1 := by
  fin_cases b <;> first | exact Or.inl rfl | exact Or.inr rfl
theorem bit_ne_iff (a b : Bit) : a≠b ↔ a=b+1 := by
  rcases bit_cases a with rfl|rfl <;>
    rcases bit_cases b with rfl|rfl <;> decide

/-- Each real containing block has exactly two diagonal classes. -/
theorem diagonal_index_two (a : Point) :
    relativeIndex diagonal.val coarse.val a=2 := by
  let x : Point := ⟨a.u,a.v,0,0,0⟩
  let y : Point := ⟨a.u,a.v,1,0,0⟩
  have hx : coarseSetoid a x := by simp [x]
  have hy : coarseSetoid a y := by simp [y]
  let qx : RelativeClass diagonal.val coarse.val a := Quotient.mk _ ⟨x,hx⟩
  let qy : RelativeClass diagonal.val coarse.val a := Quotient.mk _ ⟨y,hy⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨qx,qy,?_,?_⟩
  · intro heq
    have hd := Quotient.exact heq
    have hd' : diagonalSetoid x y := hd
    have : (0:Bit)=1 := by simpa [x,y] using ((diagonal_iff x y).mp hd').2.2
    exact zero_ne_one this
  · apply Set.eq_univ_iff_forall.mpr
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    have hz : a.u=z.val.u ∧ a.v=z.val.v := (coarse_iff a z.val).mp z.property
    rcases bit_cases (z.val.p+z.val.q) with h0|h1
    · exact Or.inl (Quotient.sound (by
        apply (diagonal_iff z.val x).mpr
        simp only [x,Point.u,Point.v,Point.p,Point.q,add_zero]
        exact ⟨hz.1.symm,hz.2.symm,h0⟩))
    · exact Or.inr (Quotient.sound (by
        apply (diagonal_iff z.val y).mpr
        simp only [y,Point.u,Point.v,Point.p,Point.q,add_zero]
        exact ⟨hz.1.symm,hz.2.symm,h1⟩))

/-- Arbitrary unary orientations are constant on the two classes and
different on different classes in each containing block. -/
structure Orientation (P : Point → Bit) : Prop where
  same : ∀ x y, diagonalSetoid x y → P x=P y
  opposite : ∀ x y, coarseSetoid x y → ¬diagonalSetoid x y → P x≠P y

def orientationOffset (P : Point → Bit) (u v : Nat) : Bit :=
  P ⟨u,v,0,0,0⟩

/-- Conversely every offset function really defines an orientation.
In particular the universal obstruction is not vacuous. -/
theorem orientation_of_offset (h : Nat → Nat → Bit) :
    Orientation (fun x => x.p+x.q+h x.u x.v) := by
  constructor
  · intro x y hxy
    obtain ⟨hu,hv,hs⟩ := (diagonal_iff x y).mp hxy
    rw [hu,hv,hs]
  · intro x y hxy hn he
    obtain ⟨hu,hv⟩ := (coarse_iff x y).mp hxy
    apply hn
    apply (diagonal_iff x y).mpr
    refine ⟨hu,hv,?_⟩
    rw [hu,hv] at he
    exact add_right_cancel he

/-- C28, the actual orientation equation: no definability, equivariance,
homogeneity or compatibility of the function h is assumed. -/
theorem orientation_normal_form {P : Point → Bit} (hP : Orientation P) (x : Point) :
    P x=x.p+x.q+orientationOffset P x.u x.v := by
  let z : Point := ⟨x.u,x.v,0,0,0⟩
  have hX : coarseSetoid x z := by simp [z]
  change P x=x.p+x.q+P z
  rcases bit_cases (x.p+x.q) with h0|h1
  · rw [h0,zero_add]
    exact hP.same x z (by simp [z,h0])
  · rw [h1]
    have hne : ¬diagonalSetoid x z := by
      intro h
      have hh := ((diagonal_iff x z).mp h).2.2
      simp [z,h1] at hh
    exact ((bit_ne_iff (P x) (P z)).mp (hP.opposite x z hX hne)).trans (add_comm _ _)

end CCO.OrbitalCover.Example
