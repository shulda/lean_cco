import CCO.RankInduction.FactorPoints
import CCO.RankInduction.OrbitalEquivalence
import CCO.RelativeMI.SequentialUse
import CCO.Owners.Master.ActionNaturality

/-! Transport of an actual relative-MI witness onto its native original
owner sort, retaining entire prescribed actions and all sparse requests. -/
universe v w t z
namespace CCO.RankInduction.Factors.NativeTransport
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization Owners.Product Owners.Provider RelativeMI

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (J : ColourEq S ()) (A0 : Finset M) (B : Finset (Coarse S H J))
variable (overA0 : ∀ x : ↥A0, coarseOwner S H J x.val ∈ B)
variable {safe : Set (S.Atom () ())}
variable (W : OriginalWitness S H J A0 B overA0 safe)
local instance nativeTransportCoarseAction : MulAction G (Coarse S H J) :=
  originalQuotientAction S H J

variable {O : Type z} [MulAction G O]
variable (e : Coarse S H J ≃ O) (he : ∀ (g : G) b, e (g • b) = g • e b)
variable (nativeB : Set O) (E : ↥B ≃ nativeB) (hE : ∀ b, (E b).val = e b.val)

def projection (x : M) : O := e (coarseOwner S H J x)

include he in
theorem projection_equivariant (g : G) (x : M) :
    projection S H J e (g • x) = g • projection S H J e x := by
  change e (g • coarseOwner S H J x) = g • e (coarseOwner S H J x)
  exact he g (coarseOwner S H J x)

omit [MulAction G O] in
include E hE in
theorem over (x : W.carrier) : projection S H J e x.val ∈ nativeB := by
  rw [projection, ← hE ⟨coarseOwner S H J x.val, W.over x⟩]
  exact (E ⟨coarseOwner S H J x.val, W.over x⟩).property

omit [MulAction G O] in
include E hE in
theorem onto : Function.Surjective
    (ownerProjection (projection S H J e) W.carrier nativeB
      (over S H J A0 B overA0 W e nativeB E hE)) := by
  intro b
  obtain ⟨x, hx⟩ := W.onto (E.symm b)
  refine ⟨x, Subtype.ext ?_⟩
  change e (coarseOwner S H J x.val) = b.val
  calc
    e (coarseOwner S H J x.val) = (E (ownerProjection (coarseOwner S H J)
        W.carrier (↑B) W.over x)).val :=
          (hE (ownerProjection (coarseOwner S H J) W.carrier (↑B) W.over x)).symm
    _ = (E (E.symm b)).val := congrArg (fun a : ↥B => (E a).val) hx
    _ = b.val := congrArg Subtype.val (E.apply_symm_apply b)

def quotient := inducedQuotient (G := G) (projection S H J e)
  (projection_equivariant S H J e he) W.carrier nativeB
  (over S H J A0 B overA0 W e nativeB E hE)
  (onto S H J A0 B overA0 W e nativeB E hE)

theorem projection_eq (x : W.carrier) :
    (quotient S H J A0 B overA0 W e he nativeB E hE).projection x =
      E ((factorQuotient S H J A0 B overA0 W).projection x) := by
  apply Subtype.ext
  change e (coarseOwner S H J x.val) =
    (E ((factorQuotient S H J A0 B overA0 W).projection x)).val
  exact (hE ((factorQuotient S H J A0 B overA0 W).projection x)).symm

theorem action_eq :
    (quotient S H J A0 B overA0 W e he nativeB E hE).action =
      (fullAutEquivOf e he E hE).toMonoidHom.comp
        (factorQuotient S H J A0 B overA0 W).action := by
  let Q := factorQuotient S H J A0 B overA0 W
  let R := quotient S H J A0 B overA0 W e he nativeB E hE
  symm
  apply Owners.Master.orbital_quotient_action_unique R
  intro β x
  change (fullAutEquivOf e he E hE (Q.action β)).val (R.projection x) =
    R.projection (β.val x)
  rw [projection_eq, fullAutEquivOf_apply, Q.action_projection]
  exact (projection_eq S H J A0 B overA0 W e he nativeB E hE (β.val x)).symm

/-- All sparse partial maps on the literal seed retain their full owner action. -/
theorem old_prescribed : PrescribedEPPAFor
    (factorQuotient S H J A0 B overA0 W) {x | x.val ∈ A0} := by
  intro p dom ran γ compatible
  let q : OrbitalPartial (G := G) (Subtype.val : ↥A0 → M) := {
    domain := {a | W.sourcePoint a ∈ p.domain}
    map a := ⟨(p.map ⟨W.sourcePoint a.val, a.property⟩).val, ran _⟩
    injective := by
      intro x y hxy
      have hv : (p.map ⟨W.sourcePoint x.val, x.property⟩).val =
          (p.map ⟨W.sourcePoint y.val, y.property⟩).val :=
        congrArg (fun a : ↥A0 => a.val) hxy
      have h := p.injective (Subtype.ext hv)
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a : p.domain => a.val.val) h
    pair x y := p.pair ⟨W.sourcePoint x.val, x.property⟩ ⟨W.sourcePoint y.val, y.property⟩ }
  let request : OriginalRequest S H J A0 B overA0 := {
    part := q
    owner := γ
    compatible a := congrArg Subtype.val (compatible ⟨W.sourcePoint a.val, a.property⟩) }
  obtain ⟨β, owner, extend⟩ := W.extensions request
  refine ⟨β, ?_, owner⟩
  intro x
  let a : ↥A0 := ⟨x.val.val, dom x.property⟩
  have ha : W.sourcePoint a = x.val := Subtype.ext rfl
  let a' : q.domain := ⟨a, by change W.sourcePoint a ∈ p.domain; rw [ha]; exact x.property⟩
  have hp := extend a'
  change (β.val (W.sourcePoint a)).val = (p.map ⟨W.sourcePoint a, a'.property⟩).val at hp
  apply Subtype.ext
  simpa only [ha] using hp

/-- The native action is prescribed on ALL owners, including empty requests. -/
theorem prescribed : PrescribedEPPAFor
    (quotient S H J A0 B overA0 W e he nativeB E hE) {x | x.val ∈ A0} := by
  let Q := factorQuotient S H J A0 B overA0 W
  let R := quotient S H J A0 B overA0 W e he nativeB E hE
  let F := fullAutEquivOf e he E hE
  intro p dom ran γ compatible
  let η := F.symm γ
  have hη (b : ↥B) : E (η.val b) = γ.val (E b) := by
    simpa only [η, F, MulEquiv.apply_symm_apply] using
      (fullAutEquivOf_apply e he E hE η b).symm
  have oldCompatible (x : p.domain) : Q.projection (p.map x) = η.val (Q.projection x.val) := by
    apply E.injective
    calc
      E (Q.projection (p.map x)) = R.projection (p.map x) :=
        (projection_eq S H J A0 B overA0 W e he nativeB E hE _).symm
      _ = γ.val (R.projection x.val) := compatible x
      _ = γ.val (E (Q.projection x.val)) := congrArg γ.val
        (projection_eq S H J A0 B overA0 W e he nativeB E hE _)
      _ = E (η.val (Q.projection x.val)) := (hη _).symm
  obtain ⟨β, extend, owner⟩ := old_prescribed S H J A0 B overA0 W p dom ran η oldCompatible
  refine ⟨β, extend, ?_⟩
  rw [action_eq]
  change F (Q.action β) = γ
  rw [owner]
  exact F.apply_symm_apply γ

/-- Arbitrary prescribed point motion uses the SAME native full owner action. -/
theorem points : GroupActions.PrescribedLift
    (quotient S H J A0 B overA0 W e he nativeB E hE).action
    (quotient S H J A0 B overA0 W e he nativeB E hE).projection := by
  let Q := factorQuotient S H J A0 B overA0 W
  let R := quotient S H J A0 B overA0 W e he nativeB E hE
  let F := fullAutEquivOf e he E hE
  intro x y γ compatible
  let η := F.symm γ
  have hη (b : ↥B) : E (η.val b) = γ.val (E b) := by
    simpa only [η, F, MulEquiv.apply_symm_apply] using
      (fullAutEquivOf_apply e he E hE η b).symm
  have oldCompatible : η.val (Q.projection x) = Q.projection y := by
    apply E.injective
    calc
      E (η.val (Q.projection x)) = γ.val (E (Q.projection x)) := hη _
      _ = γ.val (R.projection x) := congrArg γ.val
        (projection_eq S H J A0 B overA0 W e he nativeB E hE _).symm
      _ = R.projection y := compatible
      _ = E (Q.projection y) := projection_eq S H J A0 B overA0 W e he nativeB E hE _
  obtain ⟨β, owner, move⟩ := prescribed_points S H J A0 B overA0 W x y η oldCompatible
  refine ⟨β, ?_, move⟩
  rw [action_eq]
  change F (Q.action β) = γ
  rw [owner]
  exact F.apply_symm_apply γ

end
end CCO.RankInduction.Factors.NativeTransport
