import CCO.AclOwners.AclCore
import CCO.RealClosure.Bounds.Singleton
import CCO.FinitePackets.Normalization.QuotientThin

/-! Harmless actual owner imaginaries in the FULL invariant lattice.
Owner kernels may be nonexact. The proof uses ONE minimal infinite
direction for all named sorts and genuine diversity representatives,
without finite-exact normalization or a safe palette. -/

universe v w t z
namespace CCO.AclOwners
open RealClosure.Bounds RealHull.Geometry RealHull.Canonical ParityHasse.Original
open FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

/-- An actual automorphism fixes this actual quotient imaginary. The
representative is merely the quotient's `out`, never a group section. -/
def FixesOwner (K : ColourEq S ()) (q : Quotient K.val) (g : G) : Prop :=
  K q.out (g • q.out)

include H

/-- The definition is independent of the representative used to test it. -/
theorem fixesOwner_iff (K : ColourEq S ()) (q : Quotient K.val) (g : G)
    (b : M) (hb : Quotient.mk K.val b = q) :
    FixesOwner S K q g ↔ K b (g • b) := by
  have hbo : K b q.out := Quotient.exact (hb.trans (Quotient.out_eq q).symm)
  have hgb : K (g • b) (g • q.out) :=
    (class_group_invariant S () H K g b q.out).mpr hbo
  constructor
  · intro h
    exact K.val.trans hbo (K.val.trans h (K.val.symm hgb))
  · intro h
    exact K.val.trans (K.val.symm hbo) (K.val.trans h hgb)

/-- The owner stabilizer is literally the stabilizer of each quotient
point under the canonical action induced by original automorphisms. -/
theorem fixesOwner_iff_quotient_fixed (K : ColourEq S ())
    (q : Quotient K.val) (g : G) :
    letI := originalQuotientAction S H K
    FixesOwner S K q g ↔ g • q = q := by
  letI := originalQuotientAction S H K
  have hq : Quotient.mk K.val q.out = q := Quotient.out_eq q
  rw [fixesOwner_iff S H K q g q.out hq]
  constructor
  · intro h
    calc
      g • q = g • Quotient.mk K.val q.out := congrArg (fun z => g • z) hq.symm
      _ = Quotient.mk K.val (g • q.out) := rfl
      _ = Quotient.mk K.val q.out := Quotient.sound (K.val.symm h)
      _ = q := hq
  · intro h
    have he : Quotient.mk K.val (g • q.out) = Quotient.mk K.val q.out :=
      (congrArg (fun z => g • z) hq).trans (h.trans hq.symm)
    exact K.val.symm (Quotient.exact he)

/-- Real orbit over a finite real base and individually fixed actual
owner classes, possibly in several distinct full invariant sorts. -/
def ownerOrbit {I : Type z} (A : Finset M) (K : I → ColourEq S ())
    (q : ∀ i, Quotient (K i).val) (x : M) : Set M :=
  {y | ∃ g : G, (∀ a ∈ A, g • a = a) ∧
    (∀ i, FixesOwner S (K i) (q i) g) ∧ g • x = y}

def OwnerAcl {I : Type z} (A : Finset M) (K : I → ColourEq S ())
    (q : ∀ i, Quotient (K i).val) : Set M :=
  {x | (ownerOrbit S (G := G) A K q x).Finite}

/-- Naming parameters can only enlarge algebraicity. -/
theorem acl_subset_ownerAcl {I : Type z} (A : Finset M) (K : I → ColourEq S ())
    (q : ∀ i, Quotient (K i).val) : Acl G A ⊆ OwnerAcl S (G := G) A K q := by
  intro x hx
  apply hx.subset
  rintro y ⟨g,hg,_,hgy⟩
  exact ⟨g,hg,hgy⟩

/-- Original stabilizers fixing chosen actual representatives are contained
in the owner stabilizer. This is the definability-from-representatives step. -/
theorem ownerAcl_subset_representatives [DecidableEq M] {I : Type z} [Fintype I]
    (A : Finset M) (K : I → ColourEq S ()) (q : ∀ i, Quotient (K i).val)
    (b : I → M) (hb : ∀ i, Quotient.mk (K i).val (b i) = q i) :
    OwnerAcl S (G := G) A K q ⊆
      Acl G (A ∪ Finset.univ.image b) := by
  classical
  intro x hx
  apply hx.subset
  rintro y ⟨g,hg,hgy⟩
  refine ⟨g,fun a ha => hg a (Finset.mem_union_left _ ha),?_,hgy⟩
  intro i
  apply (fixesOwner_iff S H (K i) (q i) g (b i) (hb i)).mpr
  rw [hg (b i) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))]

/-- A full invariant kernel contains all minimal infinite directions. -/
def ContainsDirections (K : ColourEq S ()) : Prop :=
  ∀ D : Direction S, D.val ≤ K

/-- A bad colour has only one finite packet of neighbours in any fixed
class of the chosen direction. Equality is deliberately absent here. -/
def BadOwnerColour (D : Direction S) (p : Atom S) : Prop :=
  ∀ u z : M, D.val u z →
    (∃ y : M, col S u y = some p ∧ col S y z = some p) → finitePacket S H u z

theorem bad_neighbours_finite (D : Direction S) (p : Atom S)
    (hp : BadOwnerColour S H D p) (x c : M) :
    {b : M | D.val c b ∧ col S x b = some p}.Finite := by
  classical
  let B : Set M := {b | D.val c b ∧ col S x b = some p}
  by_cases hn : B.Nonempty
  · obtain ⟨b,hb⟩ := hn
    have hf : {z : M | finitePacket S H b z}.Finite := by
      exact Set.finite_coe_iff.mp (finitePacket_finite S H b)
    apply hf.subset
    intro z hz
    exact hp b z (D.val.val.trans (D.val.val.symm hb.1) hz.1)
      ⟨x,(col_symm S b x).trans hb.2,hz.2⟩
  · have he : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    change B.Finite
    rw [he]
    exact Set.finite_empty

omit H in
/-- Each actual old diversity edge belongs to its generated equivalence. -/
theorem atom_mem_gamma (p : Atom S) {x y : M} (h : col S x y = some p) :
    gammaEq S p x y := by
  change col S x y ∈ plus S (gamma S p).val
  rw [h,some_mem_plus]
  exact subset_generated S {p} (Set.mem_singleton _)

theorem good_owner_colour (D : Direction S) (p : Atom S)
    (hp : ¬ BadOwnerColour S H D p) : D.val ≤ gammaEq S p := by
  have hnot : ¬ FiniteClasses S (D.val ⊓ gammaEq S p) := by
    intro hf
    have hle := le_finitePacket S H _ hf
    apply hp
    intro u z huz hsq
    obtain ⟨y,huy,hyz⟩ := hsq
    exact hle ⟨huz,(gammaEq S p).val.trans (atom_mem_gamma S p huy) (atom_mem_gamma S p hyz)⟩
  by_contra hn
  have hstrict : D.val ⊓ gammaEq S p < D.val :=
    lt_of_le_of_ne inf_le_left (fun he => hn (he ▸ inf_le_right))
  exact hnot (D.property.2 _ hstrict)

/-- C29: an actual representative of ANY named owner class can be chosen
away from finitely many bad fibres AND the point x itself. -/
theorem exists_good_owner_representative (D : Direction S) (K : ColourEq S ())
    (hDK : D.val ≤ K) (q : Quotient K.val) (x : M) :
    ∃ b : M, Quotient.mk K.val b = q ∧ b ≠ x ∧
      ∃ p : Atom S, col S x b = some p ∧ D.val ≤ gammaEq S p := by
  classical
  letI := S.finiteAtom () ()
  let bad : Atom S → Set M := fun p =>
    if BadOwnerColour S H D p then {b | D.val q.out b ∧ col S x b = some p} else ∅
  have hf : ∀ p, (bad p).Finite := by
    intro p
    unfold bad
    split_ifs with hp
    · exact bad_neighbours_finite S H D p hp x q.out
    · exact Set.finite_empty
  have hforbid : ({x} ∪ ⋃ p : Atom S, bad p).Finite :=
    (Set.finite_singleton x).union (Set.finite_iUnion hf)
  have hclass : {b : M | D.val q.out b}.Infinite := by
    intro hfin
    exact D.property.1 ((finiteClasses_iff_at S H D.val q.out).mpr hfin.to_subtype)
  obtain ⟨b,hb,hboutside⟩ := hclass.diff hforbid |>.nonempty
  have hne : b ≠ x := by
    intro he
    exact hboutside (Or.inl (Set.mem_singleton_iff.mpr he))
  obtain ⟨p,hp⟩ := col_some_of_ne S (Ne.symm hne)
  have hgood : ¬ BadOwnerColour S H D p := by
    intro hbad
    apply hboutside
    right
    apply Set.mem_iUnion.mpr
    refine ⟨p,?_⟩
    change b ∈ (if BadOwnerColour S H D p then {b | D.val q.out b ∧ col S x b = some p} else ∅)
    rw [if_pos hbad]
    exact ⟨hb,hp⟩
  refine ⟨b,?_,hne,p,hp,good_owner_colour S H D p hgood⟩
  exact (Quotient.sound ((K.val.symm (hDK hb)))).trans (Quotient.out_eq q)

variable [DecidableEq M]

/-- C28: a nonalgebraic real point supplies ONE minimal infinite direction
inside every actual spoke-generated equivalence of its entire real base. -/
theorem nonalgebraic_direction (cco : SemanticCCO.{0,v,0,w} S)
    (A : Finset M) (x : M) (hx : x ∉ Acl G A) :
    ∃ hxA : x ∉ A, ∃ D : Direction S,
      ∀ a : ↥A, D.val ≤ gammaEq S (actualSpokes S A x hxA a) := by
  have hxA : x ∉ A := fun ha => hx (parameter_mem_acl A ha)
  refine ⟨hxA, ?_⟩
  have hn : ¬ ∀ D : Direction S, ∃ a : ↥A,
      ¬ D.val ≤ gammaEq S (actualSpokes S A x hxA a) :=
    fun h => hx ((algebraic_iff_directions S H cco A x hxA).mpr h)
  obtain ⟨D,hD⟩ := Classical.not_forall.mp hn
  exact ⟨D,fun a => Classical.byContradiction (fun ha => hD ⟨a,ha⟩)⟩

/-- C30: arbitrary finite mixed owner sorts containing all minimal
infinite directions do not enlarge real algebraicity. -/
theorem ownerAcl_eq_of_containsDirections (cco : SemanticCCO.{0,v,0,w} S)
    {I : Type z} [Finite I] (K : I → ColourEq S ())
    (hK : ∀ i, ContainsDirections S (K i)) (q : ∀ i, Quotient (K i).val)
    (A : Finset M) : OwnerAcl S (G := G) A K q = Acl G A := by
  classical
  letI : Fintype I := Fintype.ofFinite _
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxA
    obtain ⟨hxnot,D,hD⟩ := nonalgebraic_direction S H cco A x hxA
    have hg : ∀ i, ∃ b : M, Quotient.mk (K i).val b = q i ∧ b ≠ x ∧
        ∃ p : Atom S, col S x b = some p ∧ D.val ≤ gammaEq S p :=
      fun i => exists_good_owner_representative S H D (K i) (hK i D) (q i) x
    choose b hb hbx p hpb hDp using hg
    let B : Finset M := A ∪ Finset.univ.image b
    have hxB : x ∉ B := by
      intro hxmem
      rcases Finset.mem_union.mp hxmem with ha | hbmem
      · exact hxnot ha
      · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hbmem
        exact hbx i hi
    have halg : x ∈ Acl G B :=
      ownerAcl_subset_representatives S H A K q b hb hx
    obtain ⟨a,ha⟩ := (algebraic_iff_directions S H cco B x hxB).mp halg D
    apply ha
    rcases Finset.mem_union.mp a.property with hA | hB
    · let aA : ↥A := ⟨a.val,hA⟩
      have he : actualSpokes S B x hxB a = actualSpokes S A x hxnot aA :=
        Option.some.inj ((actualSpokes_colour S B x hxB a).symm.trans
          (actualSpokes_colour S A x hxnot aA))
      rw [he]
      exact hD aA
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hB
      have he : actualSpokes S B x hxB a = p i :=
        Option.some.inj ((actualSpokes_colour S B x hxB a).symm.trans
          (by rw [← hi]; exact hpb i))
      rw [he]
      exact hDp i
  · exact acl_subset_ownerAcl S H A K q

/-- Naming every finite collection of classes of this actual invariant
kernel leaves every finite real-base algebraic closure unchanged. -/
def Harmless (K : ColourEq S ()) : Prop :=
  ∀ (A : Finset M) (n : ℕ) (q : Fin n → Quotient K.val),
    OwnerAcl S (G := G) A (fun _ : Fin n => K) q = Acl G A

/-- C31: omitting one minimal infinite direction gives an explicit singleton
real base and one actual owner name with strictly enlarged real acl. -/
theorem omitted_direction_enlarges (cco : SemanticCCO.{0,v,0,w} S)
    (K : ColourEq S ()) (D : Direction S) (hDK : ¬ D.val ≤ K) :
    ∃ u x : M, x ∉ Acl G {u} ∧
      x ∈ OwnerAcl S (G := G) {u} (fun _ : Fin 1 => K)
        (fun _ => Quotient.mk K.val x) := by
  classical
  have hmeet : D.val ⊓ K < D.val :=
    lt_of_le_of_ne inf_le_left (fun he => hDK (he ▸ inf_le_right))
  have hfmeet : FiniteClasses S (D.val ⊓ K) := D.property.2 _ hmeet
  obtain ⟨u⟩ := S.nonemptySort ()
  have hclass : {x : M | D.val u x}.Infinite := by
    intro hf
    exact D.property.1 ((finiteClasses_iff_at S H D.val u).mpr hf.to_subtype)
  have hpacket : {x : M | finitePacket S H u x}.Finite :=
    Set.finite_coe_iff.mp (finitePacket_finite S H u)
  obtain ⟨x,hux,hxF⟩ := hclass.diff hpacket |>.nonempty
  refine ⟨u,x,?_,?_⟩
  · intro hx
    exact hxF (by simpa only [acl_singleton S H cco u] using hx)
  · have hf : {y : M | (D.val ⊓ K) x y}.Finite :=
      Set.finite_coe_iff.mp (hfmeet x)
    apply hf.subset
    rintro y ⟨g,hg,howner,rfl⟩
    have hgu : g • u = u := hg u (Finset.mem_singleton_self _)
    have hE : D.val u (g • x) := by
      have h := (class_group_invariant S () H D.val g u x).mpr hux
      rwa [hgu] at h
    refine ⟨D.val.val.trans (D.val.val.symm hux) hE,?_⟩
    exact (fixesOwner_iff S H K (Quotient.mk K.val x) g x rfl).mp (howner 0)

variable [sourceCountable : Countable M]
include sourceCountable

/-- C32, actual source headline: harmlessness is exactly containment of ALL
minimal infinite directions of the FULL invariant lattice. No exactness,
normalization, safe palette, SAP or master construction is an input. -/
theorem harmless_iff_containsDirections (cco : SemanticCCO.{0,v,0,w} S)
    [Infinite M] (K : ColourEq S ()) :
    Harmless S (G := G) K ↔ ContainsDirections S K := by
  classical
  constructor
  · intro h D
    by_contra hDK
    obtain ⟨u,x,hnot,hyes⟩ := omitted_direction_enlarges S H cco K D hDK
    exact hnot (by rw [h {u} 1 (fun _ => Quotient.mk K.val x)] at hyes; exact hyes)
  · intro h A n q
    exact ownerAcl_eq_of_containsDirections S H cco (fun _ : Fin n => K) (fun _ => h) q A

/-- The same criterion applies simultaneously to arbitrary finite mixed
collections of actual named quotient sorts. -/
theorem mixed_harmless_owners (cco : SemanticCCO.{0,v,0,w} S)
    [Infinite M] {I : Type z} [Finite I] (K : I → ColourEq S ())
    (hK : ∀ i, ContainsDirections S (K i)) (q : ∀ i, Quotient (K i).val)
    (A : Finset M) : OwnerAcl S (G := G) A K q = Acl G A :=
  ownerAcl_eq_of_containsDirections S H cco K hK q A

end CCO.AclOwners
