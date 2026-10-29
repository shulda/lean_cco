import CCO.RelativeMI.InflatedSpans
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

namespace CCO.RelativeMI
noncomputable section
universe u
private theorem nonempty_of_safePair {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X) (safe : ∀ i j, S.Menu i j)
    {p q : Sigma X} {i j : ι} (hi : p.1 = i) (hj : q.1 = j)
    (h : SafeReadings.SafePair S safe p q) : (safe i j).Nonempty := by
  rcases p with ⟨i',x⟩
  rcases q with ⟨j',y⟩
  dsimp only at hi hj
  subst i'; subst j'
  obtain ⟨a,ha,_⟩ := h
  exact ⟨a,ha⟩

/-- The empty-base case produces a genuine safe atom even on a single
owner fibre; nonemptiness is a conclusion, never a provider premise. -/
theorem strongSafe_nonempty {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X) (safe : ∀ i j, S.Menu i j)
    (h : SafeReadings.StrongSafeAmalgamation S safe) (i j : ι) :
    (safe i j).Nonempty := by
  classical
  let x : X i := Classical.choice (S.nonemptySort i)
  let y : X j := Classical.choice (S.nonemptySort j)
  let p : Sigma X := ⟨i,x⟩
  let q : Sigma X := ⟨j,y⟩
  let C : FiniteInduced (X := X) := ⟨∅,Set.finite_empty⟩
  let A : FiniteInduced (X := X) := ⟨{p},Set.finite_singleton _⟩
  let B : FiniteInduced (X := X) := ⟨{q},Set.finite_singleton _⟩
  let ca := inducedInclusion S C A (by simp [C])
  let cb := inducedInclusion S C B (by simp [C])
  obtain ⟨D,l,r,_,_,hs⟩ := h.amalgamate C A B ca cb
  let a : ↥A.vertices := ⟨p,by simp [A]⟩
  let b : ↥B.vertices := ⟨q,by simp [B]⟩
  apply nonempty_of_safePair S safe (l.preserves_sort a) (r.preserves_sort b)
  exact hs a b (fun c => False.elim c.property) (fun c => False.elim c.property)
end
end CCO.RelativeMI

namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge SafeReadings
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (U : Finset (Owner S H R)) (hU : PacketInvariant S H R U)
variable (safe : Set (S.Atom () ()))
local notation "K" => ResidualData.PacketGroup S H
local notation "N" => NamedCarrier S H R U
local notation "T" => TransversalSource.source S H R U
local notation "V" => TransversalSource.Carrier S H R U
local notation "tbl" => TransversalAge.limitTable S H R U

omit [Infinite M] in
private theorem moved_origins_separated {I : Type*}
    (point : I × K → N)
    (hm : ∀ x g h, point (x,g*h) = packetPoint S H R U hU g (point (x,h)))
    (hinj : Function.Injective point) (f : NamedAut S H R U) :
    ∀ x y, x ≠ y → ¬ finitePacket S H (f.val (point (x,1))).val
      (f.val (point (y,1))).val := by
  intro x y hxy
  exact protected_origins_separated S H R U hU
    (fun p => f.val (point p))
    (fun x g h => (congrArg f.val (hm x g h)).trans
      (namedAut_commutes S H R U hU f g (point (x,h)))) Set.univ
    (fun _ _ _ _ he => hinj (f.val.injective he)) x (Set.mem_univ _) y (Set.mem_univ _) hxy


include hU in
/-- ALL finite complete typed spans acquire orbit-safe cross atoms by
inflating the entire span, applying original closed-S amalgamation, and
reading one separated origin chart back into the actual U. -/
theorem orbitSafe_amalgamation
    (hSafe : AclOwners.StrongClosedAmalgamation S G safe) :
    StrongSafeAmalgamation T (orbitSafe S H R U hU safe) := by
  classical
  constructor
  intro C A B ca cb
  let : Finite ↥C.vertices := C.finite_vertices.to_subtype
  let : Finite ↥A.vertices := A.finite_vertices.to_subtype
  let : Finite ↥B.vertices := B.finite_vertices.to_subtype
  let d := inflatedSpan S H R U hU C A B ca cb
  obtain ⟨f,g,hFix,hStrong,hCross⟩ := packet_safe_motions S H R U hU safe hSafe
    d.base d.left d.right d.base_closed d.left_closed d.right_closed
    d.base_subset_left d.base_subset_right
  let l : ↥A.vertices → N := fun a => f.val (d.leftOrigin a)
  let r : ↥B.vertices → N := fun b => g.val (d.rightOrigin b)
  have hl : Function.Injective l := by
    intro a b he
    exact congrArg Prod.fst (d.leftPoint_injective (f.val.injective he))
  have hr : Function.Injective r := by
    intro a b he
    exact congrArg Prod.fst (d.rightPoint_injective (g.val.injective he))
  have hlsep := moved_origins_separated S H R U hU d.leftPoint d.leftPoint_move
    d.leftPoint_injective f
  have hrsep := moved_origins_separated S H R U hU d.rightPoint d.rightPoint_move
    d.rightPoint_injective g
  have hcrossPacket (a : ↥A.vertices) (b : ↥B.vertices)
      (hF : finitePacket S H (l a).val (r b).val) : l a = r b := by
    obtain ⟨k,hk,_⟩ := translation_regular S (finitePacket S H) H (R.packet_thin S H)
      (l a).val (r b).val hF
    have he : f.val (d.leftPoint (a,k)) = g.val (d.rightPoint (b,1)) := by
      rw [d.leftPoint_eq,namedAut_commutes]
      exact Subtype.ext hk
    have hh := (hStrong _ (d.leftPoint_mem a k) _ (d.rightPoint_mem b 1)).mp he
    have hphase := ((d.point_cross a b k 1).mp hh.1).2
    have he' : packetPoint S H R U hU k (l a) = r b := Subtype.ext hk
    simpa only [hphase,packetPoint_one] using he'
  let Q : Set N := Set.range l ∪ Set.range r
  have hQ : Q.Finite := (Set.finite_range l).union (Set.finite_range r)
  let : Finite ↥Q := hQ.to_subtype
  have hsep : ∀ x y : ↥Q, x ≠ y → ¬ finitePacket S H x.val.val y.val.val := by
    rintro ⟨x,hx⟩ ⟨y,hy⟩ hxy hF
    apply hxy
    apply Subtype.ext
    rcases hx with ⟨a,rfl⟩ | ⟨a,rfl⟩ <;>
      rcases hy with ⟨b,rfl⟩ | ⟨b,rfl⟩
    · by_cases hab : a = b
      · exact congrArg l hab
      · exact False.elim (hlsep a b hab hF)
    · exact hcrossPacket a b hF
    · exact (hcrossPacket b a ((finitePacket S H).val.symm hF)).symm
    · by_cases hab : a = b
      · exact congrArg r hab
      · exact False.elim (hrsep a b hab hF)
  obtain ⟨u,huo,huc⟩ := embed_origins S H R U (fun x : ↥Q => x.val) hsep
  let z : ↥Q ↪ Sigma V := {
    toFun x := (TransversalSource.sigmaEquiv S H R U).symm (u x)
    inj' := fun x y he => u.injective
      ((TransversalSource.sigmaEquiv S H R U).symm.injective he) }
  let ql (a : ↥A.vertices) : ↥Q := ⟨l a,Or.inl ⟨a,rfl⟩⟩
  let qr (b : ↥B.vertices) : ↥Q := ⟨r b,Or.inr ⟨b,rfl⟩⟩
  have hzo (x : ↥Q) : (z x).1 = ownerLabel S H R U x.val := huo x
  have hzc (x y : ↥Q) : (tbl).colour (z x).2.val (z y).2.val =
      col S x.val.val y.val.val := huc x y
  have hlo (a : ↥A.vertices) : (z (ql a)).1 = a.val.1 :=
    (hzo _).trans ((Subtype.ext (NamedAut.owner_fixed f _)).trans (d.leftOrigin_owner a))
  have hro (b : ↥B.vertices) : (z (qr b)).1 = b.val.1 :=
    (hzo _).trans ((Subtype.ext (NamedAut.owner_fixed g _)).trans (d.rightOrigin_owner b))
  have hlc (a b : ↥A.vertices) :
      (tbl).colour (z (ql a)).2.val (z (ql b)).2.val =
        (tbl).colour a.val.2.val b.val.2.val :=
    (hzc _ _).trans ((NamedAut.colour_fixed f _ _).trans (d.leftOrigin_colour a b))
  have hrc (a b : ↥B.vertices) :
      (tbl).colour (z (qr a)).2.val (z (qr b)).2.val =
        (tbl).colour a.val.2.val b.val.2.val :=
    (hzc _ _).trans ((NamedAut.colour_fixed g _ _).trans (d.rightOrigin_colour a b))
  let D : FiniteInduced (X := V) := ⟨Set.range z,Set.finite_range z⟩
  let e : InducedEmbedding T A D := {
    toEmbedding := {
      toFun a := ⟨z (ql a),⟨ql a,rfl⟩⟩
      inj' := fun a b he => hl (congrArg Subtype.val
        (z.injective (congrArg Subtype.val he))) }
    preserves_sort := hlo
    preserves_colours := fun a b => TransversalSource.tagged_eq S H R U
      (hlo a).symm (hlo b).symm (hlc a b).symm }
  let e' : InducedEmbedding T B D := {
    toEmbedding := {
      toFun a := ⟨z (qr a),⟨qr a,rfl⟩⟩
      inj' := fun a b he => hr (congrArg Subtype.val
        (z.injective (congrArg Subtype.val he))) }
    preserves_sort := hro
    preserves_colours := fun a b => TransversalSource.tagged_eq S H R U
      (hro a).symm (hro b).symm (hrc a b).symm }
  have hbase (c : ↥C.vertices) : l (ca.toEmbedding c) = r (cb.toEmbedding c) := by
    change f.val (d.leftOrigin _) = g.val (d.rightOrigin _)
    have hc := hFix (d.basePoint (c,1)) (d.basePoint_mem c 1)
    exact hc.1.trans (hc.2.symm.trans (congrArg g.val (d.origin_commutes c)))
  refine ⟨D,e,e',?_,?_,?_⟩
  · intro c
    apply Subtype.ext
    apply congrArg z
    exact Subtype.ext (hbase c)
  · intro a b he
    have he' : l a = r b := congrArg Subtype.val
      (z.injective (congrArg Subtype.val he))
    have hh := (hStrong _ (d.leftPoint_mem a 1) _ (d.rightPoint_mem b 1)).mp he'
    exact ((d.point_cross a b 1 1).mp hh.1).1
  · intro a b ha hb
    change SafePair T (orbitSafe S H R U hU safe) (z (ql a)) (z (qr b))
    have hmatrix (k : K) : ∃ c ∈ safe,
        col S (packetPoint S H R U hU k (l a)).val (r b).val = some c := by
      have hh := hCross (d.leftPoint (a,k)) (d.leftPoint_mem a k)
        (d.leftPoint_offbase a ha k) (d.rightPoint (b,1)) (d.rightPoint_mem b 1)
        (d.rightPoint_offbase b hb 1)
      simpa only [d.leftPoint_eq,namedAut_commutes,InflatedSpan.rightOrigin,l,r] using hh
    obtain ⟨c,hc,hcol⟩ := hmatrix 1
    have hcraw : (tbl).colour (z (ql a)).2.val (z (qr b)).2.val = some c :=
      (hzc _ _).trans (by simpa only [packetPoint_one] using hcol)
    cases he : (T).colour (z (ql a)).2 (z (qr b)).2 with
    | none =>
      have hh := TransversalSource.colour_map S H R U (z (ql a)).2 (z (qr b)).2
      change ((T).colour (z (ql a)).2 (z (qr b)).2).map Subtype.val = _ at hh
      rw [he,hcraw] at hh
      cases hh
    | some atom =>
      refine ⟨atom,?_,he⟩
      intro k
      obtain ⟨c,hc,hcol⟩ := hmatrix k
      have hatom := (TransversalSource.colour_some_iff S H R U _ _ atom).mp he
      have hraw : col S (l a).val (r b).val = some atom.val := (hzc _ _).symm.trans hatom
      have hswitch := two_endpoint_transport S (finitePacket S H) H (R.packet_thin S H)
        k 1 (l a).val (r b).val
      rw [mul_one,hraw] at hswitch
      have hname : (TransversalGauge.leftEquiv S H R U hU k _ _ atom).val = c := by
        apply Option.some.inj
        exact (TransversalGauge.leftEquiv_label S H R U hU k atom).trans
          (hswitch.symm.trans (by
            change col S (packetPoint S H R U hU k (l a)).val
              (packetPoint S H R U hU 1 (r b)).val = some c
            rw [packetPoint_one]
            exact hcol))
      rw [hname]
      exact hc

include hU in
/-- The genuine orbit-safe system has no additional realization or
nonemptiness premise and uses no diagonal-subgroup assumption. -/
theorem orbitSafe_system
    (hSafe : AclOwners.StrongClosedAmalgamation S G safe) :
    SafeSystem T (orbitSafe S H R U hU safe) where
  nonempty := strongSafe_nonempty T _ (orbitSafe_amalgamation S H R U hU safe hSafe)
  opposite := orbitSafe_opposite S H R U hU safe
  amalgamation := orbitSafe_amalgamation S H R U hU safe hSafe

end
end CCO.RelativeMI
