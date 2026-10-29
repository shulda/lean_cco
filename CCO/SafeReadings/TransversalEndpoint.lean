import CCO.SafeReadings.TransversalPure
import CCO.SafeReadings.TransversalGaugeTriangles
import CCO.SafeReadings.RectangularReadings

/-! The supplied endpoint laws are now discharged for the ACTUAL U
source. Original countability enters only this construction, not the
abstract moving-reading theorems. -/
universe v w t
namespace CCO.SafeReadings.TransversalPure
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge TransversalSource
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

/-- The actual finite elementary abelian thin group. -/
@[instance_reducible] def thinCommGroup : CommGroup (ResidualData.PacketGroup S H) :=
  translationCommGroup S (finitePacket S H) H (R.packet_thin S H)

/-- Every EndpointGauge obligation is discharged by the actual B025 U
and the thin translations, without faithful owners or a lifting section. -/
def endpointGauge :
    letI := thinCommGroup S H R
    EndpointGauge (source S H R B) (pureAction S H R B hB) (ResidualData.PacketGroup S H) := by
  letI := thinCommGroup S H R
  exact {
    square := translation_square S (finitePacket S H) H (R.packet_thin S H)
    owner := TransversalGauge.ownerHom S H R B hB
    switch := TransversalGauge.switchHom S H R
    left := fun g {i j} => TransversalGauge.leftEquiv S H R B hB g i j
    right := fun g {i j} => TransversalGauge.rightEquiv S H R B hB g i j
    left_label := fun g _ _ a => TransversalGauge.leftEquiv_label S H R B hB g a
    right_label := fun g _ _ a => TransversalGauge.rightEquiv_label S H R B hB g a
    triangle_left := fun g _ _ _ a b c => TransversalGauge.triangle_left S H R B hB g a b c
    triangle_right := fun g _ _ _ a b c => TransversalGauge.triangle_right S H R B hB g a b c
    diagonal := diagonal S H R B hB
    diagonal_owner := diagonal_val S H R B hB
    commute := commute S H R B hB }

/-- Proper prescribed pure owner subgroups are allowed. -/
def subgroupRelabelling (Δ : Subgroup (Gamma S H R B)) :
    PaletteRelabelling (source S H R B) Δ (FullColour S) where
  owner := (tagHom S H R B).comp Δ.subtype
  label := fun a => some a.val
  label_injective := fun _ _ _ _ he => Subtype.ext (Option.some.inj he)
  transport := fun γ _ _ a => ⟨palette S H R B hB γ.val a,rfl⟩
  converse_label := fun _ => rfl
  triangle := by
    intro γ i j k a b c a' b' c' ha hb hc
    have hae : a'.val = a.val := Option.some.inj ha
    have hbe : b'.val = b.val := Option.some.inj hb
    have hce : c'.val = c.val := Option.some.inj hc
    rw [source_triangle_iff_original S H R B,source_triangle_iff_original S H R B,hae,hbe,hce]

def subgroupAction (Δ : Subgroup (Gamma S H R B)) :
    Selectors.PureTagAction (source S H R B) Δ (FullColour S) :=
  (subgroupRelabelling S H R B hB Δ).pureAction

theorem subgroup_literalConverse (Δ : Subgroup (Gamma S H R B)) :
    LiteralConverse (source S H R B) (subgroupAction S H R B hB Δ) :=
  (subgroupRelabelling S H R B hB Δ).literalConverse

/-- The exact chosen-subgroup condition is containment of the actual
thin owner action. No faithful action or lifting section is required. -/
def subgroupEndpointGauge (Δ : Subgroup (Gamma S H R B))
    (hΔ : ∀ g, diagonal S H R B hB g ∈ Δ) :
    letI := thinCommGroup S H R
    EndpointGauge (source S H R B) (subgroupAction S H R B hB Δ) (ResidualData.PacketGroup S H) := by
  letI := thinCommGroup S H R
  exact {
    square := translation_square S (finitePacket S H) H (R.packet_thin S H)
    owner := TransversalGauge.ownerHom S H R B hB
    switch := TransversalGauge.switchHom S H R
    left := fun g {i j} => TransversalGauge.leftEquiv S H R B hB g i j
    right := fun g {i j} => TransversalGauge.rightEquiv S H R B hB g i j
    left_label := fun g _ _ a => TransversalGauge.leftEquiv_label S H R B hB g a
    right_label := fun g _ _ a => TransversalGauge.rightEquiv_label S H R B hB g a
    triangle_left := fun g _ _ _ a b c => TransversalGauge.triangle_left S H R B hB g a b c
    triangle_right := fun g _ _ _ a b c => TransversalGauge.triangle_right S H R B hB g a b c
    diagonal := fun g => ⟨diagonal S H R B hB g,hΔ g⟩
    diagonal_owner := fun _ => rfl
    commute := fun γ g i => commute S H R B hB γ.val g i }

end
end CCO.SafeReadings.TransversalPure
