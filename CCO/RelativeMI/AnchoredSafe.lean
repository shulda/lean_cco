import CCO.RelativeMI.OwnerHelpers
import CCO.RelativeMI.OrbitSafe
import CCO.AclOwners.ClosedAmalgamation

/-! The original closed-S hypothesis is applied only to ABSOLUTELY closed
real spans. Aligning the WHOLE common anchored base restores every actual
named owner, before any typed transversal conclusion is read off. -/
universe v w t
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge AclOwners
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (U : Finset (Owner S H R)) (hU : PacketInvariant S H R U)
local notation "N" => NamedCarrier S H R U

include hU in
/-- Relative packet closedness implies the required ABSOLUTE real closure
because the accepted residual source proves acl_Q=F_Q[-]. -/
theorem absolute_closed_of_packetClosed (A : Finset N) (hA : PacketClosed S H R U A) :
    Closed G (realBase S H R U A) := by
  change Acl G (realBase S H R U A) = _
  rw [R.real_acl S H]
  ext y
  constructor
  · rintro ⟨x,hx,hxy⟩
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    let y' : N := ⟨y,packet_mem_named S H R U hU a y hxy⟩
    exact Finset.mem_image.mpr ⟨y',hA a ha y' hxy,rfl⟩
  · intro hy
    exact ⟨y,hy,(finitePacket S H).val.refl y⟩

omit [Countable M] [DecidableEq M] [Infinite M] in
include H in
/-- A finite original-language induced embedding extends to one ACTUAL
original motion; in particular its full packet coordinates are retained. -/
theorem realEmbedding_motion (A : Finset M) (f : RealInducedEmbedding S A) :
    ∃ g : G, ∀ x ∈ A, g • x = f.map x := by
  let src : ↥A → Sigma (fun _ : Unit => M) := fun x => ⟨(),x.val⟩
  let dst : ↥A → Sigma (fun _ : Unit => M) := fun x => ⟨(),f.map x.val⟩
  have hc : ∀ x y, taggedColour S (src x) (src y) = taggedColour S (dst x) (dst y) := by
    intro x y
    exact congrArg (fun c : FullColour S =>
      (⟨(),(),c⟩ : Σ i : Unit,Σ j : Unit,Option (S.Atom i j)))
      (f.colours x.val x.property y.val y.property).symm
  obtain ⟨g,hg⟩ := H.extends_finite_diagram src dst hc
  refine ⟨g,?_⟩
  intro x hx
  exact eq_of_heq (Sigma.mk.inj (hg ⟨x,hx⟩)).2

/-- Fixing one actual point over EVERY displayed owner fixes those entire
owner classes. No faithful or free action on owner labels is assumed. -/
def namedMotionOfAnchors (C : Finset N)
    (hAll : ∀ s : ↥U, ∃ x ∈ C, ownerLabel S H R U x = s)
    (g : G) (hFix : ∀ x ∈ C, g • x.val = x.val) : NamedAut S H R U := by
  letI := originalQuotientAction S H R.E
  apply restrictMotion S H R U g
  intro q hq
  obtain ⟨x,hx,hOwn⟩ := hAll ⟨q,hq⟩
  have ho : owner S H R x.val = q := congrArg Subtype.val hOwn
  calc
    g • q = g • owner S H R x.val := congrArg (fun q => g • q) ho.symm
    _ = owner S H R (g • x.val) := rfl
    _ = owner S H R x.val := congrArg (owner S H R) (hFix x hx)
    _ = q := ho

variable (safe : Set (S.Atom () ()))
variable (hSafe : StrongClosedAmalgamation S G safe)
include hU hSafe in
/-- Original strong-S amalgamation becomes actual named motions after
alignment of the ENTIRE common owner-complete anchored base. -/
theorem anchored_safe_motions (C L P : Finset N)
    (hC : PacketClosed S H R U C) (hL : PacketClosed S H R U L)
    (hP : PacketClosed S H R U P) (hCL : C ⊆ L) (hCP : C ⊆ P)
    (hAll : ∀ s : ↥U, ∃ x ∈ C, ownerLabel S H R U x = s) :
    ∃ f g : NamedAut S H R U,
      (∀ x ∈ C, f.val x = x ∧ g.val x = x) ∧
      (∀ x ∈ L, ∀ y ∈ P, f.val x = g.val y ↔ x = y ∧ x ∈ C) ∧
      (∀ x ∈ L, x ∉ C → ∀ y ∈ P, y ∉ C →
        ∃ a ∈ safe, col S (f.val x).val (g.val y).val = some a) := by
  let C₀ := realBase S H R U C
  let L₀ := realBase S H R U L
  let P₀ := realBase S H R U P
  have hCL₀ : C₀ ⊆ L₀ := Finset.image_mono Subtype.val hCL
  have hCP₀ : C₀ ⊆ P₀ := Finset.image_mono Subtype.val hCP
  obtain ⟨f,g,hAgree,hStrong,hCross⟩ := hSafe C₀ L₀ P₀
    (absolute_closed_of_packetClosed S H R U hU C hC)
    (absolute_closed_of_packetClosed S H R U hU L hL)
    (absolute_closed_of_packetClosed S H R U hU P hP) hCL₀ hCP₀
  obtain ⟨f₀,hf₀⟩ := realEmbedding_motion S H L₀ f
  obtain ⟨g₀,hg₀⟩ := realEmbedding_motion S H P₀ g
  let src : ↥C → Sigma (fun _ : Unit => M) := fun x => ⟨(),f.map x.val.val⟩
  let dst : ↥C → Sigma (fun _ : Unit => M) := fun x => ⟨(),x.val.val⟩
  have hColours : ∀ x y, taggedColour S (src x) (src y) = taggedColour S (dst x) (dst y) := by
    intro x y
    exact congrArg (fun c : FullColour S =>
      (⟨(),(),c⟩ : Σ i : Unit,Σ j : Unit,Option (S.Atom i j)))
      (f.colours x.val.val ((mem_realBase S H R U L x.val).mpr (hCL x.property))
        y.val.val ((mem_realBase S H R U L y.val).mpr (hCL y.property)))
  obtain ⟨k,hk⟩ := H.extends_finite_diagram src dst hColours
  have hk' (x : N) (hx : x ∈ C) : k • f.map x.val = x.val :=
    eq_of_heq (Sigma.mk.inj (hk ⟨x,hx⟩)).2
  have hFixL : ∀ x ∈ C, (k*f₀) • x.val = x.val := by
    intro x hx
    rw [mul_smul,hf₀ x.val ((mem_realBase S H R U L x).mpr (hCL hx)),hk' x hx]
  have hFixP : ∀ x ∈ C, (k*g₀) • x.val = x.val := by
    intro x hx
    rw [mul_smul,hg₀ x.val ((mem_realBase S H R U P x).mpr (hCP hx)),
      ← hAgree x.val ((mem_realBase S H R U C x).mpr hx),hk' x hx]
  let F := namedMotionOfAnchors S H R U C hAll (k*f₀) hFixL
  let K := namedMotionOfAnchors S H R U C hAll (k*g₀) hFixP
  have hF (x : N) (hx : x ∈ L) : (F.val x).val = k • f.map x.val := by
    change (k*f₀) • x.val = _
    rw [mul_smul,hf₀ x.val ((mem_realBase S H R U L x).mpr hx)]
  have hK (x : N) (hx : x ∈ P) : (K.val x).val = k • g.map x.val := by
    change (k*g₀) • x.val = _
    rw [mul_smul,hg₀ x.val ((mem_realBase S H R U P x).mpr hx)]
  refine ⟨F,K,?_,?_,?_⟩
  · intro x hx
    exact ⟨Subtype.ext (hFixL x hx),Subtype.ext (hFixP x hx)⟩
  · intro x hx y hy
    constructor
    · intro he
      have hm : f.map x.val = g.map y.val := by
        apply MulAction.injective k
        exact (hF x hx).symm.trans ((congrArg Subtype.val he).trans (hK y hy))
      have hh := (hStrong x.val ((mem_realBase S H R U L x).mpr hx)
        y.val ((mem_realBase S H R U P y).mpr hy)).mp hm
      exact ⟨Subtype.ext hh.1,(mem_realBase S H R U C x).mp hh.2⟩
    · rintro ⟨rfl,hxC⟩
      exact (Subtype.ext (hFixL x hxC)).trans (Subtype.ext (hFixP x hxC)).symm
  · intro x hx hxC y hy hyC
    obtain ⟨a,ha,hcol⟩ := hCross x.val ((mem_realBase S H R U L x).mpr hx)
      (fun h => hxC ((mem_realBase S H R U C x).mp h))
      y.val ((mem_realBase S H R U P y).mpr hy)
      (fun h => hyC ((mem_realBase S H R U C y).mp h))
    refine ⟨a,ha,?_⟩
    rw [hF x hx,hK y hy,col_invariant S H k]
    exact hcol


include hU hSafe in
/-- Adjoin a disjoint owner-complete helper to the common base, then remove
it from the conclusion. This is genuine original-S amalgamation of actual
full packet factors, with all original named owners restored literally. -/
theorem packet_safe_motions (A L P : Finset N)
    (hA : PacketClosed S H R U A) (hL : PacketClosed S H R U L)
    (hP : PacketClosed S H R U P) (hAL : A ⊆ L) (hAP : A ⊆ P) :
    ∃ f g : NamedAut S H R U,
      (∀ x ∈ A, f.val x = x ∧ g.val x = x) ∧
      (∀ x ∈ L, ∀ y ∈ P, f.val x = g.val y ↔ x = y ∧ x ∈ A) ∧
      (∀ x ∈ L, x ∉ A → ∀ y ∈ P, y ∉ A →
        ∃ a ∈ safe, col S (f.val x).val (g.val y).val = some a) := by
  classical
  obtain ⟨T,hT,hDisj,hAll⟩ := disjoint_owner_helper S H R U hU (L ∪ P)
  have hLT (x : N) (hx : x ∈ L) : x ∉ T :=
    fun h => Finset.disjoint_left.mp hDisj h (Finset.mem_union_left _ hx)
  have hPT (x : N) (hx : x ∈ P) : x ∉ T :=
    fun h => Finset.disjoint_left.mp hDisj h (Finset.mem_union_right _ hx)
  have hC := packetClosed_union S H R U A T hA hT
  have hL' := packetClosed_union S H R U L T hL hT
  have hP' := packetClosed_union S H R U P T hP hT
  have hCL : A ∪ T ⊆ L ∪ T := Finset.union_subset_union hAL (fun _ h => h)
  have hCP : A ∪ T ⊆ P ∪ T := Finset.union_subset_union hAP (fun _ h => h)
  have hAll' : ∀ s : ↥U, ∃ x ∈ A ∪ T, ownerLabel S H R U x = s := by
    intro s
    obtain ⟨x,hx,ho⟩ := hAll s
    exact ⟨x,Finset.mem_union_right _ hx,ho⟩
  obtain ⟨f,g,hFix,hStrong,hCross⟩ := anchored_safe_motions S H R U hU safe hSafe
    (A ∪ T) (L ∪ T) (P ∪ T) hC hL' hP' hCL hCP hAll'
  refine ⟨f,g,fun x hx => hFix x (Finset.mem_union_left _ hx),?_,?_⟩
  · intro x hx y hy
    constructor
    · intro he
      obtain ⟨hxy,hxC⟩ := (hStrong x (Finset.mem_union_left _ hx)
        y (Finset.mem_union_left _ hy)).mp he
      refine ⟨hxy,?_⟩
      rcases Finset.mem_union.mp hxC with h | h
      · exact h
      · exact False.elim (hLT x hx h)
    · rintro ⟨hxy,hxA⟩
      exact (hStrong x (Finset.mem_union_left _ hx) y (Finset.mem_union_left _ hy)).mpr
        ⟨hxy,Finset.mem_union_left _ hxA⟩
  · intro x hx hxA y hy hyA
    apply hCross x (Finset.mem_union_left _ hx) _ y (Finset.mem_union_left _ hy)
    · intro hyC
      rcases Finset.mem_union.mp hyC with h | h
      · exact hyA h
      · exact hPT y hy h
    · intro hxC
      rcases Finset.mem_union.mp hxC with h | h
      · exact hxA h
      · exact hLT x hx h

end
end CCO.RelativeMI
