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

/-- The stipulated FULL coarse group orbit of the original seed is B. -/
def CoarseOrbitCover : Prop :=
  ∀ b : ↥B, ∃ γ : OrbitalAut G (Coarse S H J) (Subtype.val : ↥B → Coarse S H J),
    ∃ a : ↥A0, γ.val (ownerProjection (coarseOwner S H J) (↑A0) (↑B) overA0 a) = b

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

def owner (x : V) : ↥B := ⟨coarseOwner S H J (W.real x),W.over x⟩

@[instance_reducible] def ownerAction : MulAction K ↥B where
  smul g b := (W.coarse g).val b
  one_smul b := by
    change (W.coarse 1).val b = b
    rw [map_one]
    rfl
  mul_smul g h b := by
    change (W.coarse (g*h)).val b = (W.coarse g).val ((W.coarse h).val b)
    rw [map_mul]
    rfl

theorem owner_coverage (orbit : CoarseOrbitCover S H J A0 B overA0) :
    (W.owner S H J A0 B overA0) '' W.trimmed S H J A0 B overA0 = Set.univ := by
  let := W.ownerAction S H J A0 B overA0
  apply Trim.owner_coverage (W.packet S H J A0 B overA0) (W.seed S H J A0 B overA0)
    (W.owner S H J A0 B overA0) (fun g x => Subtype.ext (W.coarse_real g x))
  apply Set.eq_univ_of_forall
  intro b
  obtain ⟨γ,a,ha⟩ := orbit b
  obtain ⟨g,hg⟩ := W.coarse_surjective γ
  obtain ⟨x,hx⟩ := W.source a.val a.property
  have hxseed : x ∈ W.seed S H J A0 B overA0 := by
    change W.real x ∈ A0
    rw [hx]
    exact a.property
  refine ⟨g,W.owner S H J A0 B overA0 x,⟨x,hxseed,rfl⟩,?_⟩
  change (W.coarse g).val (W.owner S H J A0 B overA0 x) = b
  rw [hg]
  have howner : W.owner S H J A0 B overA0 x =
      ownerProjection (coarseOwner S H J) (↑A0) (↑B) overA0 a :=
    Subtype.ext (congrArg (coarseOwner S H J) hx)
  exact (congrArg γ.val howner).trans ha

theorem actual_over (x : W.actualCarrier S H J A0 B overA0) :
    coarseOwner S H J x.val ∈ B := by
  obtain ⟨v,_,hv⟩ := x.property
  rw [← hv]
  exact W.over v

theorem actual_onto (orbit : CoarseOrbitCover S H J A0 B overA0) :
    Function.Surjective (ownerProjection (coarseOwner S H J)
      (W.actualCarrier S H J A0 B overA0) (↑B) (W.actual_over S H J A0 B overA0)) := by
  intro b
  have hb : b ∈ (W.owner S H J A0 B overA0) '' W.trimmed S H J A0 B overA0 := by
    rw [W.owner_coverage S H J A0 B overA0 orbit]
    trivial
  obtain ⟨v,hv,hb⟩ := hb
  exact ⟨⟨W.real v,v,hv,rfl⟩,hb⟩

def realEquiv : W.trimmed S H J A0 B overA0 ≃ W.actualCarrier S H J A0 B overA0 :=
  Equiv.Set.image (W.real : V → M) (W.trimmed S H J A0 B overA0) W.real.injective

def actualPerm (g : K) : Equiv.Perm (W.actualCarrier S H J A0 B overA0) :=
  (W.realEquiv S H J A0 B overA0).permCongr
    (Trim.restrictPerm (W.packet S H J A0 B overA0) (W.seed S H J A0 B overA0) g)

theorem actualPerm_real (g : K) (v : W.trimmed S H J A0 B overA0) :
    (W.actualPerm S H J A0 B overA0 g (W.realEquiv S H J A0 B overA0 v)).val = W.real (g • v.val) := by
  change ((W.realEquiv S H J A0 B overA0)
    (Trim.restrictPerm (W.packet S H J A0 B overA0) (W.seed S H J A0 B overA0) g
      ((W.realEquiv S H J A0 B overA0).symm ((W.realEquiv S H J A0 B overA0) v)))).val = _
  rw [Equiv.symm_apply_apply]
  rfl

def actualAut (g : K) : OrbitalAut G M
    (Subtype.val : W.actualCarrier S H J A0 B overA0 → M) := by
  refine ⟨W.actualPerm S H J A0 B overA0 g,(mem_orbitalAut_iff _).mpr ?_⟩
  intro x y
  obtain ⟨v,rfl⟩ := (W.realEquiv S H J A0 B overA0).surjective x
  obtain ⟨u,rfl⟩ := (W.realEquiv S H J A0 B overA0).surjective y
  apply S.pair_homogeneous_of_homogeneous H
  have hc := W.colours g v.val u.val
  rw [W.actualPerm_real S H J A0 B overA0,W.actualPerm_real S H J A0 B overA0]
  exact hc.symm

theorem actualAut_real (g : K) (v : W.trimmed S H J A0 B overA0) :
    ((W.actualAut S H J A0 B overA0 g).val (W.realEquiv S H J A0 B overA0 v)).val = W.real (g • v.val) :=
  W.actualPerm_real S H J A0 B overA0 g v

theorem actualAut_coarse (g : K) (x : W.actualCarrier S H J A0 B overA0) :
    coarseOwner S H J ((W.actualAut S H J A0 B overA0 g).val x).val =
      ((W.coarse g).val (ownerProjection (coarseOwner S H J)
        (W.actualCarrier S H J A0 B overA0) (↑B) (W.actual_over S H J A0 B overA0) x)).val := by
  obtain ⟨v,rfl⟩ := (W.realEquiv S H J A0 B overA0).surjective x
  rw [W.actualAut_real S H J A0 B overA0]
  exact W.coarse_real g v.val

def thinRange : Subgroup K := W.thin.range

theorem thinRange_packet (g : W.thinRange S H J A0 B overA0) (x : V) :
    (W.packet S H J A0 B overA0).r ((g:K) • x) x := by
  obtain ⟨e,he⟩ := g.property
  change finitePacket S H (W.real ((g:K) • x)) (W.real x)
  rw [← he,W.thin_real]
  exact (finitePacket S H).val.symm (translation_in_packet S (finitePacket S H) G e (W.real x))

theorem thinRange_regular (x y : V) (hxy : (W.packet S H J A0 B overA0).r x y) :
    ∃ g : W.thinRange S H J A0 B overA0, (g:K) • x = y := by
  obtain ⟨e,he,_⟩ := translation_regular S (finitePacket S H) H W.packetThin (W.real x) (W.real y) hxy
  refine ⟨⟨W.thin e,⟨e,rfl⟩⟩,?_⟩
  apply W.real.injective
  exact (W.thin_real e x).trans he

/-- One global thin correction handles a selected root AFTER any
whole-clique transport. A one-packet set needs no unsafe premise at all. -/
theorem rooted_aut (Z : Set (W.actualCarrier S H J A0 B overA0))
    (unsafeZ : UnsafeSet S Subtype.val safe Z)
    (z : W.actualCarrier S H J A0 B overA0) (hz : z ∈ Z) :
    ∃ β : OrbitalAut G M (Subtype.val : W.actualCarrier S H J A0 B overA0 → M),
      (∀ x ∈ Z, (β.val x).val ∈ RealClosure.Bounds.packetClosure S H A0) ∧
      (β.val z).val ∈ A0 := by
  classical
  let e := W.realEquiv S H J A0 B overA0
  obtain ⟨vz,rfl⟩ := e.surjective z
  let ZV : Set V := {v | ∃ hv : v ∈ W.trimmed S H J A0 B overA0, e ⟨v,hv⟩ ∈ Z}
  have hvz : vz.val ∈ ZV := ⟨vz.property,hz⟩
  have inside : ZV ⊆ W.trimmed S H J A0 B overA0 := fun _ h => h.choose
  have unsafeV : UnsafeSet S W.real safe ZV := by
    intro x ⟨hx,hxZ⟩ y ⟨hy,hyZ⟩ hne a ha
    apply unsafeZ (e ⟨x,hx⟩) hxZ (e ⟨y,hy⟩) hyZ
      (fun he => hne (congrArg Subtype.val (e.injective he))) a
    exact ha
  have transported : ∃ g : K,
      (∀ x ∈ ZV, g • x ∈ Trim.packetHull (W.packet S H J A0 B overA0) (W.seed S H J A0 B overA0)) ∧
      g • vz.val ∈ W.seed S H J A0 B overA0 := by
    by_cases single : ∀ x ∈ ZV, (W.packet S H J A0 B overA0).r x vz.val
    · exact Trim.single_packet_root_correction (W.packet S H J A0 B overA0)
        (W.seed S H J A0 B overA0) ZV (W.thinRange S H J A0 B overA0)
        (W.packet_preserved S H J A0 B overA0) (W.thinRange_packet S H J A0 B overA0)
        (W.thinRange_regular S H J A0 B overA0) inside vz.val hvz single
    · have different : ∃ x ∈ ZV, ¬ (W.packet S H J A0 B overA0).r x vz.val := by
        by_contra hn
        apply single
        intro x hx
        by_contra hpacket
        exact hn ⟨x,hx,hpacket⟩
      obtain ⟨x,hx,hpacket⟩ := different
      obtain ⟨δ,hδ⟩ := W.multipacket ZV unsafeV ⟨x,hx,vz.val,hvz,hpacket⟩
      exact Trim.root_correction (W.packet S H J A0 B overA0) (W.seed S H J A0 B overA0)
        ZV (W.thinRange S H J A0 B overA0) (W.thinRange_packet S H J A0 B overA0)
        (W.thinRange_regular S H J A0 B overA0) δ
        (fun v hv => (W.hull_iff S H J A0 B overA0 _).mpr (hδ v hv)) vz.val hvz
  obtain ⟨g,hg,hroot⟩ := transported
  refine ⟨W.actualAut S H J A0 B overA0 g,?_,?_⟩
  · intro x hxZ
    obtain ⟨v,hv⟩ := e.surjective x
    have hvZ : v.val ∈ ZV := ⟨v.property,by rwa [hv]⟩
    rw [← hv,W.actualAut_real S H J A0 B overA0]
    exact (W.hull_iff S H J A0 B overA0 _).mp (hg v.val hvZ)
  · rw [W.actualAut_real S H J A0 B overA0]
    exact hroot

/-- C38--C42 on ONE fixed world: actual original-language finite
witness, exact coarse support, all requested components and rooted MI. -/
def witness [Finite V] (orbit : CoarseOrbitCover S H J A0 B overA0) :
    OriginalWitness S H J A0 B overA0 safe where
  carrier := W.actualCarrier S H J A0 B overA0
  finite := (Set.toFinite (W.trimmed S H J A0 B overA0)).image W.real
  contains := W.actual_contains S H J A0 B overA0
  closed := fun _ hx y hxy => W.actual_closed S H J A0 B overA0 hx y hxy
  over := W.actual_over S H J A0 B overA0
  onto := W.actual_onto S H J A0 B overA0 orbit
  extensions := by
    intro r
    obtain ⟨g,hcoarse,hpoint⟩ := W.requests r
    have hc : (inducedQuotient (coarseOwner S H J) (fun _ _ => rfl)
        (W.actualCarrier S H J A0 B overA0) (↑B) (W.actual_over S H J A0 B overA0)
        (W.actual_onto S H J A0 B overA0 orbit)).action (W.actualAut S H J A0 B overA0 g) = W.coarse g := by
      apply induced_owner_unique (coarseOwner S H J) (fun _ _ => rfl)
        (W.actualCarrier S H J A0 B overA0) (↑B) (W.actual_over S H J A0 B overA0)
        (W.actual_onto S H J A0 B overA0 orbit) (W.actualAut S H J A0 B overA0 g) (W.coarse g)
      intro x
      exact Subtype.ext (W.actualAut_coarse S H J A0 B overA0 g x).symm
    refine ⟨W.actualAut S H J A0 B overA0 g,hc.trans hcoarse,?_⟩
    intro x
    let u : W.actualCarrier S H J A0 B overA0 := ⟨x.val.val,
      W.actual_contains S H J A0 B overA0 ⟨x.val.val,x.val.property,(finitePacket S H).val.refl _⟩⟩
    obtain ⟨v,hv⟩ := (W.realEquiv S H J A0 B overA0).surjective u
    change ((W.actualAut S H J A0 B overA0 g).val u).val = _
    rw [← hv,W.actualAut_real S H J A0 B overA0]
    exact hpoint x v.val (congrArg Subtype.val hv)
  rooted := W.rooted_aut S H J A0 B overA0

@[simp] theorem witness_carrier [Finite V] (orbit : CoarseOrbitCover S H J A0 B overA0) :
    (W.witness S H J A0 B overA0 orbit).carrier = W.actualCarrier S H J A0 B overA0 := rfl

end FixedWorld
end
end CCO.RelativeMI
