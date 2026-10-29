import CCO.SafeReadings.TransversalGaugeRealization
import CCO.SafeReadings.TransversalSource
import CCO.SafeReadings.EndpointGauge

universe v w t
namespace CCO.SafeReadings.TransversalGauge
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge TransversalSource
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
def moveOwner (g : ResidualData.PacketGroup S H) (b : ↥B) : ↥B :=
  (packetOwnerSetAction S H R B hB).smul g b

@[simp] theorem moveOwner_twice (g : ResidualData.PacketGroup S H) (b : ↥B) :
    moveOwner S H R B hB g (moveOwner S H R B hB g b) = b := by
  letI := packetOwnerSetAction S H R B hB
  change g • (g • b) = b
  rw [←mul_smul,translation_square S (finitePacket S H) H (R.packet_thin S H),one_smul]

/-- An actual switched pair is realized on the original U owner fibres.
This does not identify owner labels with packet phases. -/
theorem palette_move (g h : ResidualData.PacketGroup S H) {b c : ↥B}
    (a : Palette S H R B b c) :
    ∃ a' : Palette S H R B (moveOwner S H R B hB g b) (moveOwner S H R B hB h c),
      (some a'.val : FullColour S) = switchColour S (finitePacket S H) (g*h) (some a.val) := by
  letI := packetOwnerSetAction S H R B hB
  obtain ⟨x,y,hxy⟩ := a.property.2
  have hne : x.val ≠ y.val := by
    rintro he
    rw [he,colour_diag] at hxy
    cases hxy
  let u : Bool → U S H R B := fun i => if i then y.val else x.val
  have hu : Function.Injective u := by
    intro i j he
    cases i <;> cases j
    · rfl
    · exact False.elim (hne he)
    · exact False.elim (hne he.symm)
    · rfl
  let es : Bool → ResidualData.PacketGroup S H := fun i => if i then h else g
  obtain ⟨v,ho,hc⟩ := switch_tuple S H R B hB u hu es
  have hx : (limitTable S H R B).owner x.val = b := x.property
  have hy : (limitTable S H R B).owner y.val = c := y.property
  have hvo : (limitTable S H R B).owner (v false) = g • b := by
    simpa only [es,u,Bool.false_eq_true,ite_false,hx] using ho false
  have hwo : (limitTable S H R B).owner (v true) = h • c := by
    simpa only [es,u,ite_true,hy] using ho true
  have hnon : (limitTable S H R B).colour (v false) (v true) ≠ none := by
    intro hn
    have he := (colour_none S H R B _ _).mp hn
    have := v.injective he
    cases this
  cases hh : (limitTable S H R B).colour (v false) (v true) with
  | none => exact False.elim (hnon hh)
  | some d =>
    refine ⟨⟨d,realized_nonthin S H R B _ _ d hh,⟨v false,hvo⟩,⟨v true,hwo⟩,hh⟩,?_⟩
    exact hh.symm.trans (by simpa only [es,u,Bool.false_eq_true,ite_false,ite_true,hxy] using hc false true)

/-- Every switched palette map is an actual equivalence, with literal
full-colour action. Its surjectivity uses the same involution twice. -/
def paletteEquiv (g h : ResidualData.PacketGroup S H) (b c : ↥B) :
    Palette S H R B b c ≃ Palette S H R B (moveOwner S H R B hB g b) (moveOwner S H R B hB h c) :=
  Equiv.ofBijective (fun a => (palette_move S H R B hB g h a).choose) (by
    constructor
    · intro a d he
      apply Subtype.ext
      have ha := (palette_move S H R B hB g h a).choose_spec
      have hd := (palette_move S H R B hB g h d).choose_spec
      have hh : switchColour S (finitePacket S H) (g*h) (some a.val) =
          switchColour S (finitePacket S H) (g*h) (some d.val) := ha.symm.trans ((congrArg (fun z => (some z.val : FullColour S)) he).trans hd)
      exact Option.some.inj ((switchColourPerm S (finitePacket S H) H (R.packet_thin S H) (g*h)).injective hh)
    · intro d
      obtain ⟨a,ha⟩ := palette_move S H R B hB g h d
      have hg := moveOwner_twice S H R B hB g b
      have hh := moveOwner_twice S H R B hB h c
      have hap : ∃ (x : TransversalSource.Carrier S H R B b) (y : TransversalSource.Carrier S H R B c),
          (limitTable S H R B).colour x.val y.val = some a.val := by
        obtain ⟨x,y,hxy⟩ := a.property.2
        exact ⟨⟨x.val,x.property.trans hg⟩,⟨y.val,y.property.trans hh⟩,hxy⟩
      let a' : Palette S H R B b c := ⟨a.val,a.property.1,hap⟩
      refine ⟨a',?_⟩
      apply Subtype.ext
      apply Option.some.inj
      have hn := (palette_move S H R B hB g h a').choose_spec
      have hav : (some a'.val : FullColour S) = switchColour S (finitePacket S H) (g*h) (some d.val) := ha
      rw [hn,hav,switchColour_involutive S (finitePacket S H) H (R.packet_thin S H)] )

theorem paletteEquiv_label (g h : ResidualData.PacketGroup S H) {b c : ↥B}
    (a : Palette S H R B b c) :
    (some (paletteEquiv S H R B hB g h b c a).val : FullColour S) =
      switchColour S (finitePacket S H) (g*h) (some a.val) :=
  (palette_move S H R B hB g h a).choose_spec

end
end CCO.SafeReadings.TransversalGauge
