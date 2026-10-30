import CCO.OrbitalCover.Example.Orientation
import CCO.OrbitalCover.Example.Homogeneity

/-! Actual full invariant covers, relative class counts and the explicit
compatible finer coordinate orientations. No profile reachability is
inferred from a full invariant-lattice cover. -/
namespace CCO.OrbitalCover.Example
open ParityHasse.Original
open scoped CharTwo

theorem diagonal_cover : diagonal ⋖ coarse :=
  covBy_of_relativeIndex_two source homogeneous diagonal coarse
    diagonal_le_coarse default (diagonal_index_two default)

def diagonalPalette : Set Colour := {a | ∃ b : Bit, a=(some b,some b)}

/-- C27's concrete obstruction: the coarse diagonal palette cannot be
a Cartesian box, independently of any reachable-profile theorem. -/
theorem diagonal_not_cartesian (A B : Set CoordColour) :
    diagonalPalette ≠ Set.prod A B := by
  intro he
  have h00 : (some (0:Bit),some (0:Bit)) ∈ Set.prod A B := by
    rw [←he]
    exact ⟨0,rfl⟩
  have h11 : (some (1:Bit),some (1:Bit)) ∈ Set.prod A B := by
    rw [←he]
    exact ⟨1,rfl⟩
  have h01 : (some (0:Bit),some (1:Bit)) ∈ diagonalPalette := by
    rw [he]
    exact ⟨h00.1,h11.2⟩
  obtain ⟨b,hb⟩ := h01
  have h0 : (0:Bit)=b := Option.some.inj (congrArg Prod.fst hb)
  have h1 : (1:Bit)=b := Option.some.inj (congrArg Prod.snd hb)
  exact zero_ne_one (h0.trans h1.symm)

theorem owner_pattern (x y : Point) :
    ownerSetoid x y ↔ pattern x y=(some 0,some 0) := by
  simp [owner_iff,pattern,coordinateColour_some,CharTwo.add_eq_zero,
    and_assoc,and_left_comm,and_comm]

def ownerEq : ColourEq source () := ⟨ownerSetoid,by
  intro x y x' y' h
  rw [owner_pattern,owner_pattern,pattern_of_colour h]⟩

def pSetoid : Setoid Point := Setoid.ker (fun x => (x.u,x.v,x.q))
def qSetoid : Setoid Point := Setoid.ker (fun x => (x.u,x.v,x.p))

@[simp] theorem p_iff (x y : Point) :
    pSetoid x y ↔ x.u=y.u ∧ x.v=y.v ∧ x.q=y.q := by
  change (x.u,x.v,x.q)=(y.u,y.v,y.q) ↔ _
  simp
@[simp] theorem q_iff (x y : Point) :
    qSetoid x y ↔ x.u=y.u ∧ x.v=y.v ∧ x.p=y.p := by
  change (x.u,x.v,x.p)=(y.u,y.v,y.p) ↔ _
  simp

theorem p_pattern (x y : Point) :
    pSetoid x y ↔ ∃ r : Bit, pattern x y=(some r,some 0) := by
  simp [p_iff,pattern,coordinateColour_some,CharTwo.add_eq_zero,and_assoc]
theorem q_pattern (x y : Point) :
    qSetoid x y ↔ ∃ r : Bit, pattern x y=(some 0,some r) := by
  simp [q_iff,pattern,coordinateColour_some,CharTwo.add_eq_zero,
    and_assoc,and_left_comm,and_comm]

def pEq : ColourEq source () := ⟨pSetoid,by
  intro x y x' y' h
  rw [p_pattern,p_pattern,pattern_of_colour h]⟩
def qEq : ColourEq source () := ⟨qSetoid,by
  intro x y x' y' h
  rw [q_pattern,q_pattern,pattern_of_colour h]⟩

theorem owner_le_p : ownerEq ≤ pEq := by
  intro x y h
  obtain ⟨hu,hv,hp,hq⟩ := (owner_iff x y).mp h
  exact (p_iff x y).mpr ⟨hu,hv,hq⟩
theorem owner_le_q : ownerEq ≤ qEq := by
  intro x y h
  obtain ⟨hu,hv,hp,hq⟩ := (owner_iff x y).mp h
  exact (q_iff x y).mpr ⟨hu,hv,hp⟩

private theorem relative_two_of_bit (E F : Setoid Point) (a : Point)
    (bit : Point → Bit) (x y : Point) (hx : F a x) (hy : F a y)
    (hx0 : bit x=0) (hy1 : bit y=1)
    (he : ∀ u v, F a u → F a v → (E u v ↔ bit u=bit v)) :
    relativeIndex E F a=2 := by
  let qx : RelativeClass E F a := Quotient.mk _ ⟨x,hx⟩
  let qy : RelativeClass E F a := Quotient.mk _ ⟨y,hy⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨qx,qy,?_,?_⟩
  · intro h
    have hxy := Quotient.exact h
    have hh := (he x y hx hy).mp hxy
    rw [hx0,hy1] at hh
    exact zero_ne_one hh
  · apply Set.eq_univ_iff_forall.mpr
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    rcases bit_cases (bit z.val) with h0|h1
    · exact Or.inl (Quotient.sound ((he z.val x z.property hx).mpr (h0.trans hx0.symm)))
    · exact Or.inr (Quotient.sound ((he z.val y z.property hy).mpr (h1.trans hy1.symm)))

theorem p_index_two (a : Point) : relativeIndex ownerEq.val pEq.val a=2 := by
  let x : Point := ⟨a.u,a.v,0,a.q,0⟩
  let y : Point := ⟨a.u,a.v,1,a.q,0⟩
  apply relative_two_of_bit ownerSetoid pSetoid a Point.p x y
    (by simp [x]) (by simp [y]) rfl rfl
  intro u v hu hv
  obtain ⟨hau,hav,haq⟩ := (p_iff a u).mp hu
  obtain ⟨hbu,hbv,hbq⟩ := (p_iff a v).mp hv
  simp [owner_iff,hau.symm.trans hbu,hav.symm.trans hbv,haq.symm.trans hbq]

theorem q_index_two (a : Point) : relativeIndex ownerEq.val qEq.val a=2 := by
  let x : Point := ⟨a.u,a.v,a.p,0,0⟩
  let y : Point := ⟨a.u,a.v,a.p,1,0⟩
  apply relative_two_of_bit ownerSetoid qSetoid a Point.q x y
    (by simp [x]) (by simp [y]) rfl rfl
  intro u v hu hv
  obtain ⟨hau,hav,hap⟩ := (q_iff a u).mp hu
  obtain ⟨hbu,hbv,hbp⟩ := (q_iff a v).mp hv
  simp [owner_iff,hau.symm.trans hbu,hav.symm.trans hbv,hap.symm.trans hbp]

theorem p_cover : ownerEq ⋖ pEq :=
  covBy_of_relativeIndex_two source homogeneous ownerEq pEq owner_le_p
    default (p_index_two default)
theorem q_cover : ownerEq ⋖ qEq :=
  covBy_of_relativeIndex_two source homogeneous ownerEq qEq owner_le_q
    default (q_index_two default)

/-- The added diversity atoms are the individual coordinate orbitals. -/
theorem p_difference (x y : Point) :
    pEq x y ∧ ¬ownerEq x y ↔ pattern x y=(some 1,some 0) := by
  rw [show pEq x y ↔ pSetoid x y from Iff.rfl, p_pattern,
    show ownerEq x y ↔ ownerSetoid x y from Iff.rfl,owner_pattern]
  constructor
  · rintro ⟨⟨r,hr⟩,hn⟩
    rcases bit_cases r with h0|h1
    · exact False.elim (hn (by simpa [h0] using hr))
    · simpa [h1] using hr
  · intro h
    exact ⟨⟨1,h⟩,by rw [h]; decide⟩

theorem q_difference (x y : Point) :
    qEq x y ∧ ¬ownerEq x y ↔ pattern x y=(some 0,some 1) := by
  rw [show qEq x y ↔ qSetoid x y from Iff.rfl,q_pattern,
    show ownerEq x y ↔ ownerSetoid x y from Iff.rfl,owner_pattern]
  constructor
  · rintro ⟨⟨r,hr⟩,hn⟩
    rcases bit_cases r with h0|h1
    · exact False.elim (hn (by simpa [h0] using hr))
    · simpa [h1] using hr
  · intro h
    exact ⟨⟨1,h⟩,by rw [h]; decide⟩

/-- Explicit compatible orientations: first name p, then name q in
each p-child. No claim about arbitrary fine orientations is made. -/
theorem compatible_fine_orientations :
    (∀ x y, ownerEq x y → x.p=y.p ∧ x.q=y.q) ∧
    (∀ x y, pEq x y → ¬ownerEq x y → x.p≠y.p) ∧
    (∀ x y, qEq x y → ¬ownerEq x y → x.q≠y.q) := by
  refine ⟨?_,?_,?_⟩
  · intro x y h
    exact ((owner_iff x y).mp h).2.2
  · intro x y h hn hp
    obtain ⟨hu,hv,hq⟩ := (p_iff x y).mp h
    exact hn ((owner_iff x y).mpr ⟨hu,hv,hp,hq⟩)
  · intro x y h hn hq
    obtain ⟨hu,hv,hp⟩ := (q_iff x y).mp h
    exact hn ((owner_iff x y).mpr ⟨hu,hv,hp,hq⟩)

end CCO.OrbitalCover.Example
