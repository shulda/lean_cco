import CCO.HKNReservoir.Requests

universe u v w z x
namespace CCO.HKNReservoir
noncomputable section
open AllThoseEPPA
variable {B : Type u} {K : Type v} [Group K] {Atom : Type w} {Γ : Type z} [Group Γ]
variable (tag : Γ →* Equiv.Perm B) {V : Type x}

/-- The finite-domain map is obtained by restricting ONE genuine ambient
map. This proves well-definedness on overlapping translated generators. -/
theorem saturateUsingAmbient (D : Data B K Atom V) (A : Set V) (hA : (encode D).IsClosed A)
    [Nonempty A] (h1 : ∀ x, D.move 1 x = x)
    (hmul : ∀ g h x, D.move (g*h) x = D.move g (D.move h x))
    (p : Request tag (D.restrict A hA)) (σ : ExactAut tag D) (hl : σ.lang = p.lang)
    (hmatch : ∀ x ∈ p.point.source, σ.perm x.val = (p.point x).val) :
    ∃ q : Structure.PartialAutomorphism (action tag) (encode (D.restrict A hA)),
      q.lang = p.lang ∧ q.source = saturation (D.restrict A hA) p.point.source ∧
      q.target = saturation (D.restrict A hA) p.point.target ∧
      (∀ x ∈ p.point.source, q x = p.point x) ∧
      ∀ k x, x ∈ p.point.source → q ((D.restrict A hA).move k x) = (D.restrict A hA).move k (p.point x) := by
  classical
  let E := D.restrict A hA
  let S := saturation E p.point.source
  let T := saturation E p.point.target
  have hE1 (x : A) : E.move 1 x = x := Subtype.ext (h1 x.val)
  have hEmul (g h : K) (x : A) : E.move (g*h) x = E.move g (E.move h x) := Subtype.ext (hmul g h x.val)
  have hS : (encode E).IsClosed S := saturation_closed E hEmul p.point.source
  have hT : (encode E).IsClosed T := saturation_closed E hEmul p.point.target
  have hσA (x : A) (hx : x ∈ S) : σ.perm x.val ∈ A := by
    obtain ⟨k,y,hy,he⟩ := hx
    have hv : D.move k y.val = x.val := congrArg Subtype.val he
    rw [←hv,σ.move,hmatch y hy]
    exact (isClosed_encode_iff D A).mp hA k (p.point y).val (p.point y).property
  let f : A → A := fun x => if h : σ.perm x.val ∈ A then ⟨σ.perm x.val,h⟩ else x
  have hfval (x : A) (hx : x ∈ S) : (f x).val = σ.perm x.val := by simp only [f,dite_eq_left (hσA x hx)]
  have hfmove (k : K) (x : A) (hx : x ∈ p.point.source) : f (E.move k x) = E.move k (p.point x) := by
    apply Subtype.ext
    rw [hfval _ ⟨k,x,hx,rfl⟩]
    change σ.perm (D.move k x.val) = D.move k (p.point x).val
    rw [σ.move,hmatch x hx]
  have hbij : Set.BijOn f S T := by
    refine ⟨?_,?_,?_⟩
    · rintro x ⟨k,y,hy,he⟩
      refine ⟨k,p.point y,p.point.map_source hy,?_⟩
      rw [←hfmove k y hy,he]
    · intro x hx y hy he
      apply Subtype.ext
      apply σ.perm.injective
      rw [←hfval x hx,←hfval y hy,he]
    · rintro y ⟨k,z,hz,he⟩
      let x := p.point.symm z
      have hx : x ∈ p.point.source := p.point.map_target hz
      refine ⟨E.move k x,⟨k,x,hx,rfl⟩,?_⟩
      rw [hfmove k x hx,p.point.right_inv hz,he]
  have howner (x : A) (hx : x ∈ S) : E.owner (f x) = tag p.lang (E.owner x) := by
    change D.owner (f x).val = tag p.lang (D.owner x.val)
    rw [hfval x hx,σ.owner,hl]
  have hfine (a : Atom) (x y : A) (hx : x ∈ S) (hy : y ∈ S) : E.fine a (f x) (f y) ↔ E.fine a x y := by
    change D.fine a (f x).val (f y).val ↔ D.fine a x.val y.val
    rw [hfval x hx,hfval y hy]
    exact σ.fine a x.val y.val
  have hmove (k : K) (x : A) (hx : x ∈ S) : f (E.move k x) = E.move k (f x) := by
    apply Subtype.ext
    have hclosed := (isClosed_encode_iff E S).mp hS k x hx
    rw [hfval _ hclosed]
    change σ.perm (D.move k x.val) = D.move k (f x).val
    rw [σ.move,hfval x hx]
  let q := partialOfBijOn tag E p.lang f S T hbij hS hT howner hfine hmove
  refine ⟨q,rfl,rfl,rfl,?_,hfmove⟩
  intro x hx
  change f x = p.point x
  apply Subtype.ext
  rw [hfval x (subset_saturation E hE1 p.point.source hx),hmatch x hx]

section ActualSource
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal OwnerTransversal.TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type z} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))

/-- B025 realizes this ONE finite original request and its ENTIRE global
owner component, even if its real domain is empty. -/
theorem request_ambient (A : Set (SourceCarrier S H R B))
    (hA : (sourceStructure S H R B hB).IsClosed A) [Finite A]
    (p : Request (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA)) :
    ∃ σ : ExactAut (sourceTag S H R B Δ) (sourceData S H R B hB),
      σ.lang = p.lang ∧ ∀ x ∈ p.point.source, σ.perm x.val = (p.point x).val := by
  let I := p.point.source
  let src : I → NamedCarrier S H R B := fun i => i.val.val.down
  let tgt : I → NamedCarrier S H R B := fun i => (p.point i.val).val.down
  have hcol (i j : I) : col S (tgt i).val (tgt j).val = col S (src i).val (src j).val := by
    have hf := p.fine
    cases hs : col S (src i).val (src j).val with
    | none =>
      cases ht : col S (tgt i).val (tgt j).val with
      | none => rfl
      | some a =>
        have hh := (hf a i.val j.val i.property j.property).mp ht
        change col S (src i).val (src j).val = some a at hh
        rw [hs] at hh
        cases hh
    | some a => exact (hf a i.val j.val i.property j.property).mpr hs
  have hown (i : I) : owner S H R (tgt i).val =
      (p.lang.val.val ⟨owner S H R (src i).val,(src i).property⟩).val :=
    congrArg Subtype.val (p.owner i.val i.property)
  obtain ⟨_,e,he,_,_,heo,hc,hm⟩ := prescribed_named_action S H R B hB src tgt p.lang.val
    (fun i j => (hcol i j).symm) hown
  have ho (x) : ownerLabel S H R B (e x) = sourceTag S H R B Δ p.lang (ownerLabel S H R B x) := Subtype.ext (heo x)
  let σ : ExactAut (sourceTag S H R B Δ) (sourceData S H R B hB) :=
    ExactAut.mk p.lang (liftNamedPerm S H R B e) (fun x => ho x.down)
      (fun a x y => Iff.of_eq (congrArg (· = some a) (hc x.down y.down)))
      (fun g x => ULift.ext _ _ (hm g x.down))
  refine ⟨σ,rfl,?_⟩
  intro x hx
  exact ULift.ext _ _ (he ⟨x,hx⟩)

/-- C20: the actual saturated original request is a genuine partial
Gamma-automorphism on the closed finite A, with both saturated sides and
all translation equations. No ambient EPPA premise has been added. -/
theorem saturate_request (A : Set (SourceCarrier S H R B))
    (hA : (sourceStructure S H R B hB).IsClosed A) [Finite A]
    (p : Request (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA)) :
    ∃ q : Structure.PartialAutomorphism (sourceAction S H R B Δ) (encode (finiteSourceData S H R B hB A hA)),
      q.lang = p.lang ∧ q.source = saturation (finiteSourceData S H R B hB A hA) p.point.source ∧
      q.target = saturation (finiteSourceData S H R B hB A hA) p.point.target ∧
      (∀ x ∈ p.point.source, q x = p.point x) ∧
      ∀ k x, x ∈ p.point.source → q ((finiteSourceData S H R B hB A hA).move k x) =
        (finiteSourceData S H R B hB A hA).move k (p.point x) := by
  classical
  by_cases hn : Nonempty A
  · letI := hn
    obtain ⟨σ,hl,hm⟩ := request_ambient S H R B hB Δ A hA p
    exact saturateUsingAmbient (sourceTag S H R B Δ) (sourceData S H R B hB) A hA
      (source_move_one S H R B hB) (source_move_mul S H R B hB) p σ hl hm
  · letI : IsEmpty A := not_nonempty_iff.mp hn
    refine ⟨emptyRequest (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA) p.lang,rfl,?_,?_,?_,?_⟩
    · ext x; exact isEmptyElim x
    · ext x; exact isEmptyElim x
    · intro x; exact isEmptyElim x
    · intro k x; exact isEmptyElim x
end ActualSource

end
end CCO.HKNReservoir
