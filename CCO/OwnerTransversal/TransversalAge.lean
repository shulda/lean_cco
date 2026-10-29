import CCO.OwnerTransversal.ClosedSAP
import CCO.OwnerTransversal.CountableColourLanguage

/-! The ACTUAL finite origin-transversal age.  A chart is admitted only
when it has an owner/fine-colour realization in the named source, with
origins in pairwise distinct original finite packets. -/

open scoped FirstOrder
open FirstOrder FirstOrder.Language

universe v w t
namespace CCO.OwnerTransversal.TransversalAge
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open CountableColour

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

def ownerLabel (x : NamedCarrier S H R B) : ↥B := ⟨owner S H R x.val,x.property⟩

abbrev Signature := CountableColour.language ↥B (FullColour S)

/-- An actual transversal realization retains ALL literal fine colours,
not just an equality-free safe palette or a coarsened packet label. -/
structure Realization {n : ℕ} (T : Table ↥B (FullColour S) (Fin n)) where
  point : Fin n → NamedCarrier S H R B
  owner : ∀ i, ownerLabel S H R B (point i) = T.owner i
  colours : ∀ i j, col S (point i).val (point j).val = T.colour i j
  separated : ∀ i j, i ≠ j → ¬ finitePacket S H (point i).val (point j).val

namespace Realization
variable {S H R B} {n : ℕ} {T : Table ↥B (FullColour S) (Fin n)}

theorem injective (f : Realization S H R B T) : Function.Injective f.point := by
  intro i j hij
  by_contra hne
  exact f.separated i j hne (hij ▸ (finitePacket S H).val.refl (f.point i).val)

end Realization

structure Chart where
  n : ℕ
  table : Table ↥B (FullColour S) (Fin n)
  realized : Nonempty (Realization S H R B table)

namespace Chart
variable {S H R B}

def realization (A : Chart S H R B) : Realization S H R B A.table := A.realized.some

instance : Countable (Chart S H R B) := by
  classical
  let := S.finiteAtom () ()
  exact Function.Injective.countable
    (f := fun A : Chart S H R B => (⟨A.n,A.table⟩ : Σ n, Table ↥B (FullColour S) (Fin n)))
    (by intro a b h; cases a; cases b; cases h; rfl)

def empty : Chart S H R B where
  n := 0
  table := ⟨Fin.elim0,fun i => Fin.elim0 i⟩
  realized := ⟨⟨Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩⟩

instance : Nonempty (Chart S H R B) := ⟨empty⟩

end Chart

namespace Chart
variable {S H R B}

instance (A : Chart S H R B) : (Signature S H R B).Structure (Fin A.n) := A.table.toStructure

/-- Reindex an arbitrary actual finite set of separated origins by Fin n. -/
def ofPoints {I : Type*} [Fintype I] (f : I → NamedCarrier S H R B)
    (hs : ∀ i j, i ≠ j → ¬ finitePacket S H (f i).val (f j).val) : Chart S H R B := by
  let e := Fintype.equivFin I
  let p := fun i => f (e.symm i)
  exact {
    n := Fintype.card I
    table := ⟨fun i => ownerLabel S H R B (p i),fun i j => col S (p i).val (p j).val⟩
    realized := ⟨⟨p,fun _ => rfl,fun _ _ => rfl,
      fun i j hne => hs _ _ (fun he => hne (e.symm.injective he))⟩⟩ }

/-- Actual induced substructures have finite chart representatives. -/
theorem hereditary (A : Type) [(Signature S H R B).Structure A] [Finite A]
    (Q : Chart S H R B) (e : A ↪[Signature S H R B] Fin Q.n) :
    ∃ P : Chart S H R B, Nonempty (A ≃[Signature S H R B] Fin P.n) := by
  classical
  let : Fintype A := Fintype.ofFinite _
  let f := Q.realization
  let p : A → NamedCarrier S H R B := fun a => f.point (e a)
  have hs : ∀ a b, a ≠ b → ¬ finitePacket S H (p a).val (p b).val :=
    fun a b hab => f.separated _ _ (fun hh => hab (e.injective hh))
  let P := ofPoints p hs
  let hA := Q.table.coding.ofEmbedding e
  let T := hA.table
  have hc := hA.embedding_preserves Q.table.coding e
  let k := Fintype.equivFin A
  have ho : ∀ a, P.table.owner (k a) = T.owner a := by
    intro a
    change ownerLabel S H R B (f.point (e (k.symm (k a)))) = T.owner a
    rw [Equiv.symm_apply_apply,f.owner]
    simpa only [Table.coding_table_owner] using hc.1 a
  have hh : ∀ a b, P.table.colour (k a) (k b) = T.colour a b := by
    intro a b
    change col S (f.point (e (k.symm (k a)))).val
      (f.point (e (k.symm (k b)))).val = T.colour a b
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply,f.colours]
    simpa only [Table.coding_table_colour] using hc.2 a b
  have iso : A ≃[Signature S H R B] Fin P.n := by
    have hstruct : T.toStructure = (inferInstance : (Signature S H R B).Structure A) :=
      hA.structure_eq
    exact Eq.mp (congrArg (fun i => @FirstOrder.Language.Equiv
      (Signature S H R B) A (Fin P.n) i P.table.toStructure) hstruct)
      (T.equiv P.table k ho hh)
  exact ⟨P,⟨iso⟩⟩

/-- Finite literal chart embeddings align their ACTUAL origins by one
named automorphism.  Every B-owner, including unused ones, is retained. -/
theorem align (A L : Chart S H R B) (e : Fin A.n ↪[Signature S H R B] Fin L.n) :
    ∃ f : NamedAut S H R B, ∀ a, f.val (A.realization.point a) = L.realization.point (e a) := by
  classical
  let := FinitePackets.Normalization.originalQuotientAction S H R.E
  let a := A.realization
  let l := L.realization
  have he := Table.embedding_preserves A.table L.table e
  let source : Fin A.n → M := fun i => (a.point i).val
  let target : Fin A.n → M := fun i => (l.point (e i)).val
  let q : ↥B → Owner S H R := Subtype.val
  have hReal : ∀ i j, col S (source i) (source j) = col S (target i) (target j) := by
    intro i j
    exact (a.colours i j).trans ((he.2 i j).symm.trans (l.colours (e i) (e j)).symm)
  have hOwner : ∀ i, owner S H R (source i) = owner S H R (target i) := by
    intro i
    have hi : ownerLabel S H R B (l.point (e i)) = ownerLabel S H R B (a.point i) :=
      (l.owner (e i)).trans ((he.1 i).trans (a.owner i).symm)
    exact (congrArg Subtype.val hi).symm
  have hCover : ∀ i, ∃ j, q j = owner S H R (source i) ∧ q j = owner S H R (target i) := by
    intro i
    exact ⟨⟨owner S H R (source i),(a.point i).property⟩,rfl,hOwner i⟩
  obtain ⟨g,hg,hq⟩ := residual_joint_lifting S H R source target q q hReal
    (fun _ _ => GroupActions.orbital_nonempty _ _) hCover
  let f := restrictMotion S H R B g (fun b hb => hq ⟨b,hb⟩)
  exact ⟨f,fun i => Subtype.ext (hg i)⟩

/-- AP is proved on the actual source: align the common origin span,
fix its WHOLE packet closure, and avoid every packet used on the left. -/
theorem amalgam_origins [Infinite M]
    (A L P : Chart S H R B)
    (e : Fin A.n ↪[Signature S H R B] Fin L.n)
    (d : Fin A.n ↪[Signature S H R B] Fin P.n) :
    ∃ g : NamedAut S H R B,
      (∀ a, g.val (P.realization.point (d a)) = L.realization.point (e a)) ∧
      (∀ l p, finitePacket S H (L.realization.point l).val (g.val (P.realization.point p)).val ↔
        ∃ a, e a = l ∧ d a = p) := by
  classical
  obtain ⟨a,ha⟩ := align A L e
  obtain ⟨b,hb⟩ := align A P d
  let k : NamedAut S H R B := a * b⁻¹
  have hk (i : Fin A.n) : k.val (P.realization.point (d i)) = L.realization.point (e i) := by
    change a.val (b.val.symm (P.realization.point (d i))) = _
    rw [← hb i,Equiv.symm_apply_apply,ha i]
  let C₀ := Finset.univ.image (fun i : Fin A.n => L.realization.point (e i))
  let C := namedPacketFinset S H R B C₀
  let L₀ := Finset.univ.image L.realization.point
  let P₀ := Finset.univ.image (fun i : Fin P.n => k.val (P.realization.point i))
  let Z := namedPacketFinset S H R B L₀
  obtain ⟨f,hfix,havoid⟩ := finite_closed_avoidance S H R B C P₀ Z
    (packetClosed_namedPacketFinset S H R B C₀)
  let g : NamedAut S H R B := f * k
  have hg (i : Fin A.n) : g.val (P.realization.point (d i)) = L.realization.point (e i) := by
    change f.val (k.val (P.realization.point (d i))) = _
    rw [hk i]
    exact hfix _ (subset_namedPacketFinset S H R B C₀
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  have hmem (p : Fin P.n) (hp : k.val (P.realization.point p) ∈ C) :
      ∃ i, d i = p := by
    obtain ⟨x,hx,hxp⟩ := (mem_namedPacketFinset S H R B C₀ _).mp hp
    obtain ⟨x',hx',hxv⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hx'
    have hF : finitePacket S H (k.val (P.realization.point (d j))).val
        (k.val (P.realization.point p)).val := by
      rw [hk j,hj,hxv]
      exact hxp
    have hcol := NamedAut.colour_fixed k (P.realization.point (d j)) (P.realization.point p)
    have hF' := ((finitePacket S H).property _ _ _ _ hcol).mp hF
    exact ⟨j,by by_contra hn; exact P.realization.separated _ _ hn hF'⟩
  refine ⟨g,hg,?_⟩
  intro l p
  constructor
  · intro hF
    by_cases hp : k.val (P.realization.point p) ∈ C
    · obtain ⟨i,hi⟩ := hmem p hp
      have hli : e i = l := by
        have hF' : finitePacket S H (L.realization.point l).val (L.realization.point (e i)).val := by
          simpa only [← hi,hg] using hF
        by_contra hn
        exact L.realization.separated l (e i) (Ne.symm hn) hF'
      exact ⟨i,hli,hi⟩
    · have hZ : g.val (P.realization.point p) ∈ Z := by
        apply (mem_namedPacketFinset S H R B L₀ _).mpr
        exact ⟨(L.realization.point l).val,
          (mem_realBase S H R B L₀ _).mpr (Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩),hF⟩
      exact False.elim (havoid _ (Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩) hp _ hZ rfl)
  · rintro ⟨i,rfl,rfl⟩
    rw [hg i]

/-- The finite ACTUAL transversal age has SAP, proved over arbitrary
chart embeddings, without original real-age SAP. -/
theorem strong_amalgamation [Infinite M]
    (A L P : Chart S H R B)
    (e : Fin A.n ↪[Signature S H R B] Fin L.n)
    (d : Fin A.n ↪[Signature S H R B] Fin P.n) :
    ∃ (Q : Chart S H R B) (i : Fin L.n ↪[Signature S H R B] Fin Q.n)
      (j : Fin P.n ↪[Signature S H R B] Fin Q.n),
      i.comp e = j.comp d ∧ ∀ l p, i l = j p ↔ ∃ a, e a = l ∧ d a = p := by
  classical
  obtain ⟨g,hbase,hcross⟩ := amalgam_origins A L P e d
  let l := L.realization
  let p := P.realization
  let D := Finset.univ.image l.point ∪ Finset.univ.image (fun a => g.val (p.point a))
  have hsep : ∀ x ∈ D, ∀ y ∈ D,
      finitePacket S H x.val y.val → x = y := by
    intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hy
      have hab : a = b := by by_contra hn; exact l.separated a b hn hxy
      exact congrArg l.point hab
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨c,hca,hcb⟩ := (hcross a b).mp hxy
      rw [← hca,← hcb,hbase c]
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨c,hca,hcb⟩ := (hcross b a).mp ((finitePacket S H).val.symm hxy)
      rw [← hca,← hcb,hbase c]
    · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hy
      have hc := NamedAut.colour_fixed g (p.point a) (p.point b)
      have hF := ((finitePacket S H).property _ _ _ _ hc).mp hxy
      have hab : a = b := by by_contra hn; exact p.separated a b hn hF
      exact congrArg (fun i => g.val (p.point i)) hab
  have hs : ∀ x y : ↥D, x ≠ y → ¬ finitePacket S H x.val.val y.val.val := by
    intro x y hne hF
    exact hne (Subtype.ext (hsep x.val x.property y.val y.property hF))
  let Q := ofPoints (fun x : ↥D => x.val) hs
  let z := Fintype.equivFin ↥D
  let i₀ : Fin L.n ↪ ↥D := {
    toFun a := ⟨l.point a,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)⟩
    inj' := fun _ _ h => l.injective (congrArg Subtype.val h) }
  let j₀ : Fin P.n ↪ ↥D := {
    toFun a := ⟨g.val (p.point a),Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)⟩
    inj' := fun _ _ h => p.injective (g.val.injective (congrArg Subtype.val h)) }
  let iFun := i₀.trans z.toEmbedding
  let jFun := j₀.trans z.toEmbedding
  have hio : ∀ a, Q.table.owner (iFun a) = L.table.owner a := by
    intro a
    change ownerLabel S H R B (z.symm (z (i₀ a))).val = L.table.owner a
    rw [Equiv.symm_apply_apply]
    exact l.owner a
  have hic : ∀ a b, Q.table.colour (iFun a) (iFun b) = L.table.colour a b := by
    intro a b
    change col S (z.symm (z (i₀ a))).val.val (z.symm (z (i₀ b))).val.val = _
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    exact l.colours a b
  have hjo : ∀ a, Q.table.owner (jFun a) = P.table.owner a := by
    intro a
    change ownerLabel S H R B (z.symm (z (j₀ a))).val = P.table.owner a
    rw [Equiv.symm_apply_apply]
    apply Subtype.ext
    exact (NamedAut.owner_fixed g (p.point a)).trans (congrArg Subtype.val (p.owner a))
  have hjc : ∀ a b, Q.table.colour (jFun a) (jFun b) = P.table.colour a b := by
    intro a b
    change col S (z.symm (z (j₀ a))).val.val (z.symm (z (j₀ b))).val.val = _
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    exact (NamedAut.colour_fixed g (p.point a) (p.point b)).trans (p.colours a b)
  let i := L.table.embedding Q.table iFun hio hic
  let j := P.table.embedding Q.table jFun hjo hjc
  have hcomm : i.comp e = j.comp d := by
    apply DFunLike.ext
    intro a
    change z (i₀ (e a)) = z (j₀ (d a))
    exact congrArg z (Subtype.ext (hbase a).symm)
  refine ⟨Q,i,j,hcomm,?_⟩
  intro a b
  constructor
  · intro hab
    change z (i₀ a) = z (j₀ b) at hab
    have he : l.point a = g.val (p.point b) := congrArg Subtype.val (z.injective hab)
    apply (hcross a b).mp
    rw [he]
  · rintro ⟨c,rfl,rfl⟩
    exact DFunLike.congr_fun hcomm c

/-- Empty-base SAP gives actual JEP, including an empty owner catalogue. -/
theorem joint [Infinite M] (L P : Chart S H R B) :
    ∃ (Q : Chart S H R B), Nonempty (Fin L.n ↪[Signature S H R B] Fin Q.n) ∧
      Nonempty (Fin P.n ↪[Signature S H R B] Fin Q.n) := by
  let A : Chart S H R B := empty
  let e : Fin A.n ↪[Signature S H R B] Fin L.n := {
    toFun := Fin.elim0
    inj' := fun a => Fin.elim0 a
    map_fun' F := Empty.elim F
    map_rel' := by
      intro n r x
      cases r with
      | owner _ => exact Fin.elim0 (x 0)
      | colour _ => exact Fin.elim0 (x 0) }
  let d : Fin A.n ↪[Signature S H R B] Fin P.n := {
    toFun := Fin.elim0
    inj' := fun a => Fin.elim0 a
    map_fun' F := Empty.elim F
    map_rel' := by
      intro n r x
      cases r with
      | owner _ => exact Fin.elim0 (x 0)
      | colour _ => exact Fin.elim0 (x 0) }
  obtain ⟨Q,i,j,_,_⟩ := strong_amalgamation A L P e d
  exact ⟨Q,⟨i⟩,⟨j⟩⟩

end Chart

/-- Only the chart INDEX is shrunk. Its actual owner and colour values
remain in their original universes, and its carrier is still Fin n. -/
abbrev Code := Shrink.{0} (Chart S H R B)

instance : Countable (Code S H R B) :=
  Countable.of_equiv (Chart S H R B) (equivShrink.{0} _)

instance : Nonempty (Code S H R B) :=
  ⟨equivShrink.{0} _ (Chart.empty (S := S) (H := H) (R := R) (B := B))⟩

def decode (A : Code S H R B) : Chart S H R B := (equivShrink.{0} _).symm A

def encode (A : Chart S H R B) : Code S H R B := equivShrink.{0} _ A

@[simp] theorem decode_encode (A : Chart S H R B) :
    decode S H R B (encode S H R B A) = A := (equivShrink.{0} _).symm_apply_apply A

@[simp] theorem encode_decode (A : Code S H R B) :
    encode S H R B (decode S H R B A) = A := (equivShrink.{0} _).apply_symm_apply A

abbrev Carrier (A : Code S H R B) := Fin (decode S H R B A).n

abbrev table (A : Code S H R B) : Table ↥B (FullColour S) (Carrier S H R B A) :=
  (decode S H R B A).table

instance (A : Code S H R B) : (Signature S H R B).Structure (Carrier S H R B A) :=
  (table S H R B A).toStructure

def realization (A : Code S H R B) : Realization S H R B (table S H R B A) :=
  (decode S H R B A).realization

/-- Forgetting a realized finite chart into its actual named origin set. -/
def point (A : Code S H R B) : Carrier S H R B A → NamedCarrier S H R B :=
  (realization S H R B A).point

theorem point_injective (A : Code S H R B) : Function.Injective (point S H R B A) :=
  (realization S H R B A).injective

namespace Chart
variable {S H R B}

def castEquiv {A P : Chart S H R B} (h : A = P) :
    Fin A.n ≃[Signature S H R B] Fin P.n := by
  cases h
  exact FirstOrder.Language.Equiv.refl _ _

end Chart

/-- All generic age hypotheses are discharged from the actual residual
named source.  In particular AP is not an extra source assumption. -/
def data [Infinite M] : CountableAge.Data (Signature S H R B) where
  Chart := Code S H R B
  Carrier := Carrier S H R B
  hereditary A _ _ P e := by
    obtain ⟨Q,hQ⟩ := Chart.hereditary A (decode S H R B P) e
    refine ⟨encode S H R B Q,?_⟩
    exact hQ.map (fun f => (Chart.castEquiv (decode_encode S H R B Q).symm).comp f)
  joint A P := by
    obtain ⟨Q,⟨a⟩,⟨b⟩⟩ := Chart.joint (decode S H R B A) (decode S H R B P)
    let k := (Chart.castEquiv (decode_encode S H R B Q).symm).toEmbedding
    exact ⟨encode S H R B Q,⟨k.comp a⟩,⟨k.comp b⟩⟩
  amalgamate A L P e d := by
    obtain ⟨Q,i,j,hcomm,_⟩ := Chart.strong_amalgamation
      (decode S H R B A) (decode S H R B L) (decode S H R B P) e d
    let k := (Chart.castEquiv (decode_encode S H R B Q).symm).toEmbedding
    refine ⟨encode S H R B Q,k.comp i,k.comp j,?_⟩
    apply DFunLike.ext
    intro a
    exact congrArg k (DFunLike.congr_fun hcomm a)

abbrev U [Infinite M] := (data S H R B).Limit

/-- Unique names on the finite charts give actual complete owner and
fine-colour functions on the internal chain union. -/
theorem limitCoding [Infinite M] : Coding (B := ↥B) (C := FullColour S) (U S H R B) :=
  (data S H R B).limitCoding (fun A => (table S H R B A).coding)

def limitTable [Infinite M] : Table ↥B (FullColour S) (U S H R B) :=
  (limitCoding S H R B).table

/-- Every actual finite origin chart embeds into the constructed limit,
retaining all literal owners and all ordered fine pairs. -/
theorem embed_chart [Infinite M] (Q : Chart S H R B) :
    ∃ e : Fin Q.n ↪ U S H R B,
      (∀ i, (limitTable S H R B).owner (e i) = Q.table.owner i) ∧
      (∀ i j, (limitTable S H R B).colour (e i) (e j) = Q.table.colour i j) := by
  let D := data S H R B
  obtain ⟨g⟩ := D.chart_embeds (encode S H R B Q)
  let g' : Carrier S H R B (encode S H R B Q) ↪[Signature S H R B] U S H R B := g
  let e : Fin Q.n ↪[Signature S H R B] U S H R B :=
    g'.comp (Chart.castEquiv (decode_encode S H R B Q).symm).toEmbedding
  refine ⟨⟨e,e.injective⟩,?_,?_⟩
  · intro i
    apply ((limitCoding S H R B).owner_rel (e i) _).mp
    exact (e.map_rel (Symbol.owner (Q.table.owner i)) (fun _ => i)).mpr rfl
  · intro i j
    have hh := (e.map_rel (Symbol.colour (Q.table.colour i j)) (![i,j])).mpr rfl
    exact ((limitCoding S H R B).colour_tuple (Q.table.colour i j) (e ∘ ![i,j])).mp hh

/-- Every finite tuple in the actual limit is read in one finite source
chart. Distinct tuple entries give genuinely distinct original packets. -/
theorem realize_tuple [Infinite M] {I : Type*} [Finite I] (u : I → U S H R B) :
    ∃ f : I → NamedCarrier S H R B,
      (∀ i, ownerLabel S H R B (f i) = (limitTable S H R B).owner (u i)) ∧
      (∀ i j, col S (f i).val (f j).val = (limitTable S H R B).colour (u i) (u j)) ∧
      (∀ i j, u i ≠ u j → ¬ finitePacket S H (f i).val (f j).val) := by
  let D := data S H R B
  obtain ⟨n,y,hy⟩ := DirectLimit.exists_quotient_mk'_sigma_mk'_eq
    (fun n => D.Carrier (D.stage n)) D.chain u
  have hp : ∀ i, D.intoLimit n (y i) = u i := fun i => (congrFun hy i).symm
  let Q := D.stage n
  let f := realization S H R B Q
  have ho (i : I) : (limitTable S H R B).owner (D.intoLimit n (y i)) =
      (table S H R B Q).owner (y i) := by
    apply ((limitCoding S H R B).owner_rel _ _).mp
    exact ((D.intoLimit n).map_rel
      (Symbol.owner ((table S H R B Q).owner (y i))) (fun _ => y i)).mpr rfl
  have hc (i j : I) : (limitTable S H R B).colour (D.intoLimit n (y i))
      (D.intoLimit n (y j)) = (table S H R B Q).colour (y i) (y j) := by
    have hh := ((D.intoLimit n).map_rel
      (Symbol.colour ((table S H R B Q).colour (y i) (y j))) (![y i,y j])).mpr rfl
    exact ((limitCoding S H R B).colour_tuple ((table S H R B Q).colour (y i) (y j))
      ((D.intoLimit n) ∘ ![y i,y j])).mp hh
  refine ⟨fun i => f.point (y i),?_,?_,?_⟩
  · intro i
    rw [← hp i]
    exact (f.owner (y i)).trans (ho i).symm
  · intro i j
    rw [← hp i,← hp j]
    exact (f.colours (y i) (y j)).trans (hc i j).symm
  · intro i j hij
    apply f.separated (y i) (y j)
    intro heq
    exact hij ((hp i).symm.trans ((congrArg (D.intoLimit n) heq).trans (hp j)))

end
end CCO.OwnerTransversal.TransversalAge
