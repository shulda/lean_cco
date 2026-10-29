import CCO.RelativeMI.FineOwners
import CCO.FullRows.OrbitTrim
import Mathlib.Logic.Equiv.Set

/-! Actual invariant trimming of ONE fixed finite decoded world. The
inputs below are internal decoder outputs, discharged in the principal
constructor. No original-age EPPA, full automorphism equality, faithful
owner action or coherent choice of request lifts is assumed. -/
universe v w t z k
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization Owners.Product Owners.Provider
open RawExact FullRows

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (J : ColourEq S ()) (A0 : Finset M) (B : Finset (Coarse S H J))
variable (overA0 : ∀ x : ↥A0, coarseOwner S H J x.val ∈ B)
local instance : MulAction G (Coarse S H J) := originalQuotientAction S H J

/-- Singleton sets are unsafe vacuously; equality is not a new atom. -/
def UnsafeSet {V : Type z} (real : V → M) (safe : Set (S.Atom () ())) (Z : Set V) : Prop :=
  ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → ∀ a, col S (real x) (real y) = some a → a ∉ safe

/-- ONE actual decoded world before trimming. Its group may be the
semilinear permutation IMAGE; it is not required to be full Aut. -/
structure FixedWorld (safe : Set (S.Atom () ())) (V : Type z)
    (K : Type k) [Group K] [MulAction K V] where
  real : V ↪ M
  source : ∀ a ∈ A0, ∃ x, real x = a
  over : ∀ x, coarseOwner S H J (real x) ∈ B
  colours : ∀ (g : K) x y, col S (real (g • x)) (real (g • y)) = col S (real x) (real y)
  packetThin : ThinBottom S (finitePacket S H)
  thin : Translation S (finitePacket S H) G →* K
  thin_real : ∀ g x, real (thin g • x) = g.val (real x)
  coarse : K →* OrbitalAut G (Coarse S H J) (Subtype.val : ↥B → Coarse S H J)
  coarse_surjective : Function.Surjective coarse
  coarse_real : ∀ g x, coarseOwner S H J (real (g • x)) =
    ((coarse g).val ⟨coarseOwner S H J (real x),over x⟩).val
  requests : ∀ r : OriginalRequest S H J A0 B overA0,
    ∃ g : K, coarse g = r.owner ∧
      ∀ x : r.part.domain, ∀ v, real v = x.val.val → real (g • v) = (r.part.map x).val
  multipacket : ∀ Z : Set V, UnsafeSet S real safe Z →
    (∃ x ∈ Z, ∃ y ∈ Z, ¬ finitePacket S H (real x) (real y)) →
      ∃ g : K, ∀ x ∈ Z, real (g • x) ∈ RealClosure.Bounds.packetClosure S H A0

/-- The final source-relative witness, with its ACTUAL recognizable
coarse quotient and every original/empty request retained. -/
structure OriginalWitness (safe : Set (S.Atom () ())) where
  carrier : Set M
  finite : carrier.Finite
  contains : RealClosure.Bounds.packetClosure S H A0 ⊆ carrier
  closed : ∀ x ∈ carrier, ∀ y, finitePacket S H x y → y ∈ carrier
  over : ∀ x : carrier, coarseOwner S H J x.val ∈ B
  onto : Function.Surjective (ownerProjection (coarseOwner S H J) carrier (↑B) over)
  extensions : ∀ r : OriginalRequest S H J A0 B overA0,
    ∃ β : OrbitalAut G M (Subtype.val : carrier → M),
      (inducedQuotient (coarseOwner S H J) (fun _ _ => rfl)
        carrier (↑B) over onto).action β = r.owner ∧
      ∀ x : r.part.domain,
        (β.val ⟨x.val.val,contains ⟨x.val.val,x.val.property,(finitePacket S H).val.refl _⟩⟩).val =
          (r.part.map x).val
  rooted : ∀ Z : Set carrier, UnsafeSet S (Subtype.val : carrier → M) safe Z →
    ∀ z ∈ Z, ∃ β : OrbitalAut G M (Subtype.val : carrier → M),
      (∀ x ∈ Z, (β.val x).val ∈ RealClosure.Bounds.packetClosure S H A0) ∧
      (β.val z).val ∈ A0

namespace FixedWorld
variable {V : Type z} {K : Type k} [Group K] [MulAction K V]
variable {safe : Set (S.Atom () ())}
variable (W : FixedWorld S H J A0 B overA0 safe V K)

def packet : Setoid V := Setoid.comap W.real (finitePacket S H).val
def seed : Set V := W.real ⁻¹' (↑A0 : Set M)
def trimmed : Set V := Trim.orbitTrim K (W.packet S H J A0 B overA0) (W.seed S H J A0 B overA0)
def actualCarrier : Set M := W.real '' W.trimmed S H J A0 B overA0

theorem packet_preserved (g : K) {x y : V}
    (hxy : (W.packet S H J A0 B overA0).r x y) :
    (W.packet S H J A0 B overA0).r (g • x) (g • y) :=
  ((finitePacket S H).property _ _ _ _ (W.colours g x y).symm).mp hxy

/-- The abstract packet hull is EXACTLY the original full F[A0] on
this actual image, not merely a named-source relative closure. -/
theorem hull_iff (x : V) :
    x ∈ Trim.packetHull (W.packet S H J A0 B overA0) (W.seed S H J A0 B overA0) ↔
      W.real x ∈ RealClosure.Bounds.packetClosure S H A0 := by
  constructor
  · rintro ⟨a,ha,hxa⟩
    exact ⟨W.real a,ha,(finitePacket S H).val.symm hxa⟩
  · rintro ⟨a,ha,hax⟩
    obtain ⟨v,hv⟩ := W.source a ha
    refine ⟨v,?_,?_⟩
    · change W.real v ∈ A0
      rw [hv]
      exact ha
    change finitePacket S H (W.real x) (W.real v)
    rw [hv]
    exact (finitePacket S H).val.symm hax

/-- Actual regular thin translations fill every ambient packet of a
decoded point; no extra full-packet closure premise is hidden here. -/
theorem actual_contains : RealClosure.Bounds.packetClosure S H A0 ⊆ W.actualCarrier S H J A0 B overA0 := by
  rintro x ⟨a,ha,hax⟩
  obtain ⟨v,hv⟩ := W.source a ha
  obtain ⟨e,he,_⟩ := translation_regular S (finitePacket S H) H W.packetThin a x hax
  have hr : W.real (W.thin e • v) = x := (W.thin_real e v).trans (by rw [hv,he])
  refine ⟨W.thin e • v,?_,hr⟩
  apply Trim.hull_subset_trim
  apply (W.hull_iff S H J A0 B overA0 _).mpr
  rw [hr]
  exact ⟨a,ha,hax⟩

theorem actual_closed {x : M} (hx : x ∈ W.actualCarrier S H J A0 B overA0)
    (y : M) (hxy : finitePacket S H x y) : y ∈ W.actualCarrier S H J A0 B overA0 := by
  obtain ⟨v,hv,rfl⟩ := hx
  obtain ⟨e,he,_⟩ := translation_regular S (finitePacket S H) H W.packetThin (W.real v) y hxy
  exact ⟨W.thin e • v,Trim.orbitSet_smul K _ (W.thin e) hv,(W.thin_real e v).trans he⟩

end FixedWorld
end
end CCO.RelativeMI
