import CCO.RealClosure.Bounds.Examples.PhaseCCO
import CCO.RealClosure.Bounds.Packet
import CCO.RealClosure.Bounds.Algebraicity

/-! The actual finite packet of the infinite Cartesian phase source. Every
larger original equivalence has a class containing Nat by explicit motions. -/
namespace CCO.RealClosure.Bounds.Examples.Phase
open ParityHasse.Original RealHull.Geometry

def packetEq : ColourEq source () :=
  ⟨⟨fun x y => row x = row y ∧ column x = column y,
    ⟨fun _ => ⟨rfl,rfl⟩,fun h => ⟨h.1.symm,h.2.symm⟩,
      fun h k => ⟨h.1.trans k.1,h.2.trans k.2⟩⟩⟩,
    fun _ _ _ _ hc => and_congr (coordinates_of_colour_eq hc).1
      (coordinates_of_colour_eq hc).2.1⟩

def packetClassEquiv (x : Point) : ClassPoint source () packetEq x ≃ Bool where
  toFun y := phase y.val
  invFun b := ⟨(row x,column x,b),⟨rfl,rfl⟩⟩
  left_inv y := by
    apply Subtype.ext
    exact Prod.ext y.property.1 (Prod.ext y.property.2 rfl)
  right_inv _ := rfl

theorem packet_finite : FiniteClasses source packetEq :=
  fun x => Finite.of_injective (packetClassEquiv x) (packetClassEquiv x).injective

theorem packet_card (x : Point) : Nat.card (ClassPoint source () packetEq x) = 2 := by
  rw [Nat.card_congr (packetClassEquiv x)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_bool]

private def coordinate (b : Bool) (x : Point) : ℕ := if b then row x else column x

noncomputable def infiniteClassEmbedding (E : ColourEq source ()) (x y : Point)
    (hE : E x y) (b : Bool) (hxy : coordinate b x ≠ coordinate b y) :
    ℕ ↪ ClassPoint source () E x := by
  let N := coordinate b x + coordinate b y + 1
  let g (n : ℕ) : Aut := motion
    (if b then Equiv.swap (coordinate b y) (N+n) else 1)
    (if b then 1 else Equiv.swap (coordinate b y) (N+n)) false
  have hxN (n : ℕ) : coordinate b x ≠ N+n := by dsimp [N]; omega
  have hfix (n : ℕ) : g n • x = x := by
    cases b
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact Equiv.swap_apply_of_ne_of_ne hxy (hxN n)
        · exact Bool.false_xor (phase x)
    · apply Prod.ext
      · exact Equiv.swap_apply_of_ne_of_ne hxy (hxN n)
      · apply Prod.ext
        · rfl
        · exact Bool.false_xor (phase x)
  have himage (n : ℕ) : coordinate b (g n • y) = N+n := by
    cases b <;> simp [coordinate,g,motion,motionPerm,row,column,phase]
  refine ⟨fun n => ⟨g n • y,?_⟩,?_⟩
  · have hh := (E.property x y (g n • x) (g n • y) (aut_colour (g n) x y).symm).mp hE
    simpa only [hfix n] using hh
  · intro n m he
    have hh := congrArg (fun p : ClassPoint source () E x => coordinate b p.val) he
    rw [himage n,himage m] at hh
    exact Nat.add_left_cancel hh

theorem finite_equivalence_le_packet (E : ColourEq source ()) (hfin : FiniteClasses source E) :
    E ≤ packetEq := by
  intro x y hE
  have equal (b : Bool) : coordinate b x = coordinate b y := by
    by_contra hn
    letI := hfin x
    have hnat : Finite ℕ := Finite.of_injective (infiniteClassEmbedding E x y hE b hn)
      (infiniteClassEmbedding E x y hE b hn).injective
    letI := hnat
    exact not_finite ℕ
  exact ⟨equal true,equal false⟩

@[simp] theorem finitePacket_eq : finitePacket source homogeneous = packetEq :=
  le_antisymm (finite_equivalence_le_packet _ (finitePacket_finite source homogeneous))
    (le_finitePacket source homogeneous packetEq packet_finite)

/-- Actual original packet saturation of algebraicity, from finite orbit
images times the TWO literal phases. No model-theoretic transitivity axiom. -/
theorem acl_packet_saturated (A : Finset Point) {x y : Point}
    (hx : x ∈ Acl Aut A) (hxy : packetEq x y) : y ∈ Acl Aut A := by
  have himage : (Set.prod (orbitOver Aut A x) (Set.univ : Set Bool)).Finite :=
    hx.prod Set.finite_univ
  have hout : ((fun p : Point × Bool => (row p.1,column p.1,p.2)) ''
      Set.prod (orbitOver Aut A x) (Set.univ : Set Bool)).Finite := himage.image _
  apply hout.subset
  rintro z ⟨g,hg,rfl⟩
  refine ⟨(g • x,phase (g • y)),⟨⟨g,hg,rfl⟩,trivial⟩,?_⟩
  apply Prod.ext
  · change row (g • x) = row (g • y)
    simpa only [aut_row] using congrArg (autRow g) hxy.1
  · apply Prod.ext
    · change column (g • x) = column (g • y)
      simpa only [aut_column] using congrArg (autColumn g) hxy.2
    · rfl
end CCO.RealClosure.Bounds.Examples.Phase
