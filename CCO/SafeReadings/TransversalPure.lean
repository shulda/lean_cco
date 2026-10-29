import CCO.SafeReadings.TransversalGauge
import CCO.OwnerTransversal.PrescribedActions

universe v w t z
namespace CCO.SafeReadings.TransversalPure
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge TransversalSource Owners.Product
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
local instance : MulAction G (Owner S H R) := originalQuotientAction S H R.E

abbrev Gamma := OrbitalAut G (Owner S H R) (Subtype.val : ↥B → Owner S H R)

def tagHom : Gamma S H R B →* Equiv.Perm ↥B := (orbitalStructure G (Owner S H R) (Subtype.val : ↥B → Owner S H R)).autGroup.subtype

include hB

/-- The entire prescribed finite owner permutation is realized by ONE
original motion. This existence is not made into a group section. -/
theorem original_lift (γ : Gamma S H R B) :
    ∃ g : G, ∀ b : ↥B, g • b.val = (γ.val b).val := by
  let empty : Empty → NamedCarrier S H R B := Empty.elim
  obtain ⟨g,_,_,hg,_⟩ := prescribed_named_action S H R B hB empty empty γ
    (fun i => nomatch i) (fun i => nomatch i)
  exact ⟨g,hg⟩

/-- Every finite pure owner relabelling is realized in the actual U,
with literal colours fixed and no coherent lift or origin section. -/
theorem pure_tuple (γ : Gamma S H R B) {I : Type z} [Finite I]
    (u : I → U S H R B) (hu : Function.Injective u) :
    ∃ v : I ↪ U S H R B,
      (∀ i, (limitTable S H R B).owner (v i) = γ.val ((limitTable S H R B).owner (u i))) ∧
      ∀ i j, (limitTable S H R B).colour (v i) (v j) = (limitTable S H R B).colour (u i) (u j) := by
  obtain ⟨a,ho,hc,hs⟩ := realize_tuple S H R B u
  let empty : Empty → NamedCarrier S H R B := Empty.elim
  obtain ⟨g,e,_,hgo,hpoint,heowner,hecolour,_⟩ := prescribed_named_action S H R B hB empty empty γ
    (fun i => nomatch i) (fun i => nomatch i)
  have hp : ∀ i j, i ≠ j → ¬ finitePacket S H (e (a i)).val (e (a j)).val := by
    intro i j hij hF
    exact hs i j (fun he => hij (hu he))
      (((finitePacket S H).property _ _ _ _ (hecolour (a i) (a j))).mp hF)
  obtain ⟨v,hvo,hvc⟩ := embed_origins S H R B (fun i => e (a i)) hp
  refine ⟨v,?_,?_⟩
  · intro i
    have heo : ownerLabel S H R B (e (a i)) = γ.val (ownerLabel S H R B (a i)) :=
      Subtype.ext (heowner (a i))
    exact (hvo i).trans (heo.trans (congrArg γ.val (ho i)))
  · intro i j
    exact (hvc i j).trans ((hecolour (a i) (a j)).trans (hc i j))

/-- A literal old atom is present in the relabelled palette. -/
def palette (γ : Gamma S H R B) {b c : ↥B} (a : Palette S H R B b c) :
    Palette S H R B (γ.val b) (γ.val c) := by
  refine ⟨a.val,a.property.1,?_⟩
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
  obtain ⟨v,ho,hc⟩ := pure_tuple S H R B hB γ u hu
  have hx : (limitTable S H R B).owner x.val = b := x.property
  have hy : (limitTable S H R B).owner y.val = c := y.property
  have hvo : (limitTable S H R B).owner (v false) = γ.val b := by simpa only [u,Bool.false_eq_true,ite_false,hx] using ho false
  have hwo : (limitTable S H R B).owner (v true) = γ.val c := by simpa only [u,ite_true,hy] using ho true
  exact ⟨⟨v false,hvo⟩,⟨v true,hwo⟩,(hc false true).trans hxy⟩

@[simp] theorem palette_val (γ : Gamma S H R B) {b c : ↥B} (a : Palette S H R B b c) :
    (palette S H R B hB γ a).val = a.val := rfl

def paletteEquiv (γ : Gamma S H R B) (b c : ↥B) :
    Palette S H R B b c ≃ Palette S H R B (γ.val b) (γ.val c) :=
  Equiv.ofBijective (palette S H R B hB γ) (by
    constructor
    · intro a d he
      apply Subtype.ext
      exact congrArg (fun z : Palette S H R B (γ.val b) (γ.val c) => z.val) he
    · intro d
      let a := palette S H R B hB γ⁻¹ d
      have hb : (γ⁻¹).val (γ.val b) = b := γ.val.symm_apply_apply b
      have hc : (γ⁻¹).val (γ.val c) = c := γ.val.symm_apply_apply c
      have hap : ∃ (x : TransversalSource.Carrier S H R B b) (y : TransversalSource.Carrier S H R B c),
          (limitTable S H R B).colour x.val y.val = some a.val := by
        obtain ⟨x,y,hxy⟩ := a.property.2
        exact ⟨⟨x.val,x.property.trans hb⟩,⟨y.val,y.property.trans hc⟩,hxy⟩
      exact ⟨⟨a.val,a.property.1,hap⟩,Subtype.ext rfl⟩)

/-- Actual thin translations commute with the original quotient action. -/
theorem packetMove_original (e : ResidualData.PacketGroup S H) (g : G) (q : Owner S H R) :
    packetOwnerMove S H R e (g • q) = g • packetOwnerMove S H R e q := by
  induction q using Quotient.inductionOn with
  | _ x =>
    change owner S H R (e.val (g • x)) = owner S H R (g • e.val x)
    exact congrArg (owner S H R) (translation_equivariant S (finitePacket S H) G e g x)

/-- The central owner commutation uses ONE original lift for the finite
owner permutation; no coherent choice of these lifts is assumed. -/
theorem commute (γ : Gamma S H R B) (e : ResidualData.PacketGroup S H) (b : ↥B) :
    γ.val (TransversalGauge.moveOwner S H R B hB e b) =
      TransversalGauge.moveOwner S H R B hB e (γ.val b) := by
  obtain ⟨g,hg⟩ := original_lift S H R B hB γ
  apply Subtype.ext
  change (γ.val (TransversalGauge.moveOwner S H R B hB e b)).val = packetOwnerMove S H R e (γ.val b).val
  calc
    _ = g • packetOwnerMove S H R e b.val := (hg (TransversalGauge.moveOwner S H R B hB e b)).symm
    _ = packetOwnerMove S H R e (g • b.val) := (packetMove_original S H R B hB e g b.val).symm
    _ = _ := congrArg (packetOwnerMove S H R e) (hg b)

/-- Every actual diagonal thin owner move belongs to the FULL given
owner orbital automorphism group, including nonfaithful owner actions. -/
def diagonal (e : ResidualData.PacketGroup S H) : Gamma S H R B :=
  ⟨TransversalGauge.ownerHom S H R B hB e,(mem_orbitalAut_iff _).mpr (by
    intro b c
    let x := b.val.out
    let y := c.val.out
    obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x (e.val x) y (e.val y)
      (translation_preserves_colour S (finitePacket S H) H (R.packet_thin S H) e x y).symm
    refine ⟨g,?_,?_⟩
    · change g • b.val = packetOwnerMove S H R e b.val
      have hb : owner S H R x = b.val := Quotient.out_eq b.val
      rw [←hb]
      change owner S H R (g • x) = owner S H R (e.val x)
      exact congrArg (owner S H R) hgx
    · change g • c.val = packetOwnerMove S H R e c.val
      have hc : owner S H R y = c.val := Quotient.out_eq c.val
      rw [←hc]
      change owner S H R (g • y) = owner S H R (e.val y)
      exact congrArg (owner S H R) hgy)⟩

@[simp] theorem diagonal_val (e : ResidualData.PacketGroup S H) :
    (diagonal S H R B hB e).val = TransversalGauge.ownerHom S H R B hB e := rfl

end
end CCO.SafeReadings.TransversalPure
