import CCO.FinitePackets.Normalization.Examples.TwinPackets
import CCO.RealHull.Canonical.Hull
import CCO.FinitePackets.Geometry.MinimalCutBasic

/-! The thin-but-exact countercontrol: actual RAW profiles of r² and c²,
the nonidentity finite exact packet, minimal row cut and two-point fibre. -/
namespace CCO.FinitePackets.Normalization.Examples.Twin
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open Colour

def doubleWord (a : Colour) : RawWord source () () :=
  .atom (i := ()) (j := ()) (k := ()) a (.atom (i := ()) (j := ()) (k := ()) a (.nil ()))

theorem row_square (x y : Point) :
    RawWord.relation source (doubleWord Colour.row) x y ↔ rowEq x y := by
  constructor
  · rintro ⟨z,hxz,w,hzw,hwy⟩
    change w = y at hwy
    subst w
    exact ((colour_row x z).mp hxz).1.trans ((colour_row z y).mp hzw).1
  · intro hxy
    let c := max (column x) (column y) + 1
    have hxc : column x ≠ c := by dsimp [c]; omega
    have hcy : c ≠ column y := by dsimp [c]; omega
    let z : Point := (row x,c,false)
    exact ⟨z,(colour_row x z).mpr ⟨rfl,hxc⟩,y,(colour_row z y).mpr ⟨hxy,hcy⟩,rfl⟩

theorem column_square (x y : Point) :
    RawWord.relation source (doubleWord Colour.column) x y ↔ columnEq x y := by
  constructor
  · rintro ⟨z,hxz,w,hzw,hwy⟩
    change w = y at hwy
    subst w
    exact ((colour_column x z).mp hxz).2.trans ((colour_column z y).mp hzw).2
  · intro hxy
    let r := max (row x) (row y) + 1
    have hxr : row x ≠ r := by dsimp [r]; omega
    have hry : r ≠ row y := by dsimp [r]; omega
    let z : Point := (r,column x,false)
    exact ⟨z,(colour_column x z).mpr ⟨hxr,rfl⟩,y,(colour_column z y).mpr ⟨hry,hxy⟩,rfl⟩

theorem row_exact : ExactCRT.IsExactEq source (i := ()) rowEq.val := by
  apply isExactEq_of_word source rowEq (doubleWord Colour.row)
  funext x y
  exact propext (row_square x y)

theorem column_exact : ExactCRT.IsExactEq source (i := ()) columnEq.val := by
  apply isExactEq_of_word source columnEq (doubleWord Colour.column)
  funext x y
  exact propext (column_square x y)

theorem packet_exact : ExactCRT.IsExactEq source (i := ()) packetEq.val :=
  ExactCRT.isExactEq_inf source row_exact column_exact

theorem packet_nonidentity : packetEq ≠ ⊥ := by
  intro he
  have hh : packetEq (0,0,false) (0,0,true) := ⟨rfl,rfl⟩
  rw [he] at hh
  have hb := congrArg bit hh
  exact Bool.false_ne_true hb

def flip (x : Point) : Point := (row x,column x,!bit x)

@[simp] theorem flip_flip (x : Point) : flip (flip x) = x := by
  rcases x with ⟨r,c,b⟩; cases b <;> rfl

theorem twin_iff_flip (x y : Point) : colour x y = some twin ↔ y = flip x := by
  rw [colour_twin]
  constructor
  · rintro ⟨hr,hc,hb⟩
    apply Prod.ext (show row y = row (flip x) from hr.symm)
    apply Prod.ext (show column y = column (flip x) from hc.symm)
    change bit y = !bit x
    cases hx : bit x <;> cases hy : bit y <;> simp_all
  · rintro rfl
    refine ⟨rfl,rfl,?_⟩
    change bit x ≠ !bit x
    cases bit x <;> decide

theorem twin_thin (x : Point) : ∃! y, colour x y = some twin :=
  ⟨flip x,(twin_iff_flip _ _).mpr rfl,fun _ h => (twin_iff_flip _ _).mp h⟩

theorem twin_square_identity (x y : Point) :
    RawWord.relation source (doubleWord twin) x y ↔ x = y := by
  constructor
  · rintro ⟨z,hxz,w,hzw,hwy⟩
    change w = y at hwy
    subst w
    have hz := (twin_iff_flip x z).mp hxz
    have hy := (twin_iff_flip z y).mp hzw
    rw [hz,flip_flip] at hy
    exact hy.symm
  · rintro rfl
    refine ⟨flip x,(twin_iff_flip _ _).mpr rfl,x,?_,rfl⟩
    exact (twin_iff_flip _ _).mpr (flip_flip x).symm

theorem packet_atom_only_twin (a : Colour)
    (ha : ∃ x y : Point, packetEq x y ∧ colour x y = some a) : a = twin := by
  obtain ⟨x,y,⟨hr,hc⟩,hcol⟩ := ha
  cases a <;> simp_all

/-- Every actual diversity atom in the full finite packet is thin. -/
theorem all_packet_atoms_thin (a : Colour)
    (ha : ∃ x y : Point, packetEq x y ∧ colour x y = some a) :
    ∀ x, ∃! y, colour x y = some a := by
  rw [packet_atom_only_twin a ha]
  exact twin_thin

/-- The literal conditional c-fibre over ANY distinct target row has two
points; this is an equivalence with Bool, not just a valency inequality. -/
def conditionalFibreEquiv (x : Point) (r : ℕ) (hr : r ≠ row x) :
    {y : Point // row y = r ∧ colour x y = some Colour.column} ≃ Bool where
  toFun y := bit y.val
  invFun b := ⟨(r,column x,b),rfl,(colour_column _ _).mpr ⟨hr.symm,rfl⟩⟩
  left_inv y := by
    apply Subtype.ext
    exact Prod.ext y.property.1.symm (Prod.ext ((colour_column _ _).mp y.property.2).2 rfl)
  right_inv _ := rfl

theorem conditional_fibre_card (x : Point) (r : ℕ) (hr : r ≠ row x) :
    Nat.card {y : Point // row y = r ∧ colour x y = some Colour.column} = 2 := by
  rw [Nat.card_congr (conditionalFibreEquiv x r hr)]
  simp

private theorem row_le_of_row_pair (J : ColourEq source ()) {x y : Point}
    (hJ : J x y) (hr : colour x y = some Colour.row) : rowEq ≤ J := by
  intro u v huv
  obtain ⟨z,huz,w,hzw,hwv⟩ := (row_square u v).mpr huv
  change w = v at hwv
  subst w
  apply J.val.trans
  · exact (J.property x y u z (hr.trans huz.symm)).mp hJ
  · exact (J.property x y z v (hr.trans hzw.symm)).mp hJ

theorem row_minimal_infinite : Geometry.MinimalInfiniteCut source rowEq := by
  constructor
  · intro hfin
    have hclass := (Geometry.finiteIndex_bottom_iff_finite_classes source rowEq).mp hfin
    letI := hclass (0,0,false)
    have hh : Finite ℕ := Finite.of_injective
      (fun n : ℕ => (⟨(0,n,false),rfl⟩ : ClassPoint source () rowEq (0,0,false)))
      (fun n m he => congrArg (fun z : ClassPoint source () rowEq (0,0,false) => column z.val) he)
    letI := hh
    exact not_finite ℕ
  · intro J hJ
    apply (Geometry.finiteIndex_bottom_iff_finite_classes source J).mpr
    apply finiteClasses_of_le source (F := packetEq) ?_ packet_finite
    intro x y hxy
    refine ⟨hJ.le hxy,?_⟩
    by_contra hc
    have hr := (colour_row x y).mpr ⟨hJ.le hxy,hc⟩
    exact hJ.not_ge (row_le_of_row_pair J hxy hr)

/-- The full packet consists of actual equality and precisely the twin atom. -/
theorem packet_iff_eq_or_twin (x y : Point) :
    packetEq x y ↔ x = y ∨ colour x y = some twin := by
  constructor
  · intro hp
    by_cases he : x = y
    · exact Or.inl he
    · apply Or.inr
      apply (colour_twin x y).mpr
      refine ⟨hp.1,hp.2,?_⟩
      intro hb
      exact he (Prod.ext hp.1 (Prod.ext hp.2 hb))
  · rintro (rfl | ht)
    · exact ⟨rfl,rfl⟩
    · exact ⟨((colour_twin x y).mp ht).1,((colour_twin x y).mp ht).2.1⟩

@[simp] theorem row_inf_finitePacket : rowEq ⊓ finitePacket source homogeneous = packetEq := by
  rw [finitePacket_eq]
  exact inf_eq_right.mpr (fun _ _ h => h.1)

end CCO.FinitePackets.Normalization.Examples.Twin
