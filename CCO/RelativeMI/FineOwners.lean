import CCO.RelativeMI.NormalizedSource
import CCO.Owners.Provider.ExactFiniteBase
import CCO.Owners.Provider.Enlargement
import CCO.Owners.Provider.PacketProjection
import CCO.OwnerTransversal.NamedSource
import CCO.OwnerTransversal.TypedLifting
import CCO.AclOwners.QuotientSource

/-! C25--C26: simultaneous ORIGINAL ambient lifts precede the sole
EPPA application, whose source is Q/E. All coarse owners, including
those unused by a real request, occur in the same finite host. -/
universe v w t
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal AclOwners
open Owners.Product Owners.Provider ExactCRT RawExact

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (J : ColourEq S ())

/-- A type alias retaining the displayed original action in its type
parameters. Its elements are literally the actual coarse quotient classes. -/
abbrev Coarse (_H₀ : HomogeneousSource S G) (J₀ : ColourEq S ()) : Type v := Quotient J₀.val

local instance : MulAction G (Owner S H R) := originalQuotientAction S H R.E
local instance : MulAction G (Coarse S H J) := originalQuotientAction S H J

def coarseOwner (x : M) : Coarse S H J := Quotient.mk'' x

def fineProjection (hEJ : R.E ≤ J) : Owner S H R → Coarse S H J :=
  Abstract.quotientMap hEJ

@[simp] theorem fineProjection_owner (hEJ : R.E ≤ J) (x : M) :
    fineProjection S H R J hEJ (owner S H R x) = coarseOwner S H J x := rfl

theorem fineProjection_equivariant (hEJ : R.E ≤ J) (g : G) (q : Owner S H R) :
    fineProjection S H R J hEJ (g • q) = g • fineProjection S H R J hEJ q := by
  induction q using Quotient.inductionOn with | _ x => rfl

theorem fineProjection_surjective (hEJ : R.E ≤ J) :
    Function.Surjective (fineProjection S H R J hEJ) :=
  Abstract.quotientMap_surjective hEJ

variable (A0 : Finset M) (B : Finset (Coarse S H J))
variable (overA0 : ∀ x : ↥A0, coarseOwner S H J x.val ∈ B)

/-- Every empty real request still prescribes an arbitrary ENTIRE B
automorphism. This is the original-language request, not a fine EPPA premise. -/
abbrev OriginalRequest :=
  OwnerRequest (G := G) (coarseOwner S H J) (↑A0 : Set M) (↑B : Set (Coarse S H J)) overA0

include R in
/-- C25 checks every mixed pair using the accepted real/exact-owner
lifting theorem and obtains ONE ORIGINAL motion for each request. -/
theorem original_request_lift (hJ : IsExactEq S (i := ()) J.val)
    (r : OriginalRequest S H J A0 B overA0) :
    ∃ g : G,
      (∀ x : r.part.domain, g • x.val.val = (r.part.map x).val) ∧
      (∀ b : ↥B, g • b.val = (r.owner.val b).val) := by
  have real : ∀ x y : r.part.domain,
      S.colour (i := ()) (j := ()) x.val.val y.val.val =
        S.colour (r.part.map x).val (r.part.map y).val := by
    intro x y
    obtain ⟨g,hgx,hgy⟩ := r.part.pair x y
    have hc := col_invariant S H g x.val.val y.val.val
    rw [hgx,hgy] at hc
    exact hc.symm
  exact finite_real_owner_lifting S H R.cco J hJ
    (fun x : r.part.domain => x.val.val) (fun x => (r.part.map x).val)
    (fun b : ↥B => b.val) (fun b => (r.owner.val b).val) real
    (fun b c => orbitalAut_pair r.owner b c) (by
      intro x
      exact ⟨⟨coarseOwner S H J x.val.val,overA0 x.val⟩,rfl,(r.compatible x).symm⟩)

variable (closedB : ∀ b ∈ B, ∀ c,
  ownerPacket S H (coarseOwner S H J) Quotient.mk''_surjective (fun _ _ => rfl) b c → c ∈ B)

include overA0 closedB in
omit [Countable M] [DecidableEq M] in
/-- Greatest FINITE classes in the FULL actual coarse quotient keep
every F-saturated old point over B. No EPPA or exactness of F is used. -/
theorem old_packet_over {x : M} (hx : x ∈ RealClosure.Bounds.packetClosure S H A0) :
    coarseOwner S H J x ∈ B := by
  obtain ⟨a,ha,hax⟩ := hx
  exact closedB (coarseOwner S H J a) (overA0 ⟨a,ha⟩) _
    (packet_projection S H (coarseOwner S H J) Quotient.mk''_surjective
      (fun _ _ => rfl) a x hax)

/-- A finite fine-owner host. The extension clause retains the entire
coarse component; its EPPA provider is deliberately absent from the data. -/
structure FineBase (hEJ : R.E ≤ J) where
  carrier : Set (Owner S H R)
  finite : carrier.Finite
  contains : ∀ x ∈ RealClosure.Bounds.packetClosure S H A0, owner S H R x ∈ carrier
  over : ∀ q : carrier, fineProjection S H R J hEJ q.val ∈ B
  onto : Function.Surjective (ownerProjection (fineProjection S H R J hEJ)
    carrier (↑B : Set (Coarse S H J)) over)
  extensions : ∀ r : OriginalRequest S H J A0 B overA0,
    ∃ α : OrbitalAut G (Owner S H R) (Subtype.val : carrier → Owner S H R),
      (∀ x : r.part.domain,
        (α.val ⟨owner S H R x.val.val,
          contains x.val.val ⟨x.val.val,x.val.property,(finitePacket S H).val.refl _⟩⟩).val =
            owner S H R (r.part.map x).val) ∧
      (∀ q : carrier, fineProjection S H R J hEJ (α.val q).val =
        (r.owner.val (ownerProjection (fineProjection S H R J hEJ) carrier (↑B) over q)).val)

include closedB in
/-- C26: ONLY ordinary EPPA of the actual quotient Q/E is consumed.
Representatives of all B are adjoined BEFORE one common finite host. -/
theorem fine_base (hEJ : R.E ≤ J) (hJ : IsExactEq S (i := ()) J.val)
    (ep : OrdinaryEPPA G (Owner S H R)) :
    Nonempty (FineBase S H R J A0 B overA0 hEJ) := by
  classical
  let π := fineProjection S H R J hEJ
  let U0 : Set (Owner S H R) := (owner S H R) '' RealClosure.Bounds.packetClosure S H A0
  have hU0 : U0.Finite := (RealClosure.Bounds.packetClosure_finite S H A0).image _
  have over0 : ∀ q ∈ U0, π q ∈ B := by
    rintro q ⟨x,hx,rfl⟩
    exact old_packet_over S H J A0 B overA0 closedB hx
  let reps : ↥B → Owner S H R := fun b => (fineProjection_surjective S H R J hEJ b.val).choose
  have reps_spec (b : ↥B) : π (reps b) = b.val :=
    (fineProjection_surjective S H R J hEJ b.val).choose_spec
  let T := U0 ∪ Set.range reps
  have hT : T.Finite := hU0.union (Set.finite_range reps)
  have inc0 : U0 ⊆ T := Set.subset_union_left
  have overT : ∀ q : T, π q.val ∈ B := by
    rintro ⟨q,hq⟩
    rcases hq with hq | ⟨b,rfl⟩
    · exact over0 q hq
    · rw [reps_spec b]; exact b.property
  have ontoT : Function.Surjective (ownerProjection π T (↑B) overT) := by
    intro b
    exact ⟨⟨reps b,Or.inr ⟨b,rfl⟩⟩,Subtype.ext (reps_spec b)⟩
  let Req := OriginalRequest S H J A0 B overA0
  have lifts (r : Req) := original_request_lift S H R J A0 B overA0 hJ r
  let g : Req → G := fun r => (lifts r).choose
  have greal (r : Req) (x : r.part.domain) : g r • x.val.val = (r.part.map x).val :=
    (lifts r).choose_spec.1 x
  have gcoarse (r : Req) (b : ↥B) : g r • b.val = (r.owner.val b).val :=
    (lifts r).choose_spec.2 b
  let presentation := exactPresentation S R.exact
  have homogeneous : HomogeneousSource (actualQuotientSource S H R.E) G :=
    actualQuotient_homogeneous S H R.E presentation
      (exactPresentation_represents S R.exact) R.cco
  have prescribed_coarse (r : Req) (q : Owner S H R) (hq : π q ∈ B) :
      π ((ambientAut (A := Owner S H R) (g r)).val q) =
        (r.owner.val ⟨π q,hq⟩).val :=
    (fineProjection_equivariant S H R J hEJ (g r) q).trans (gcoarse r ⟨π q,hq⟩)
  obtain ⟨W,hW,hTW,overW,ontoW,extensions⟩ := finite_base_restriction
    (source_orbital_homogeneous (actualQuotientSource S H R.E) homogeneous) ep
    π (fineProjection_equivariant S H R J hEJ) T (↑B) hT B.finite_toSet
    overT ontoT (fun r : Req => r.owner)
    (fun r => ambientAut (A := Owner S H R) (g r)) prescribed_coarse
  have oldW (x : M) (hx : x ∈ RealClosure.Bounds.packetClosure S H A0) : owner S H R x ∈ W :=
    hTW (inc0 ⟨x,hx,rfl⟩)
  refine ⟨⟨W,hW,oldW,overW,ontoW,?_⟩⟩
  intro r
  obtain ⟨α,hα,hown⟩ := extensions r
  refine ⟨α,?_,hown⟩
  intro x
  have hx : owner S H R x.val.val ∈ T :=
    inc0 ⟨x.val.val,⟨x.val.val,x.val.property,(finitePacket S H).val.refl _⟩,rfl⟩
  exact (hα ⟨owner S H R x.val.val,hx⟩).trans
    (congrArg (owner S H R) (greal r x))

end
end CCO.RelativeMI
