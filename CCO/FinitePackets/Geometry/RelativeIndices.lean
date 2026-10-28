import CCO.FinitePackets.Geometry.Basic
import Mathlib.Data.Fintype.Sigma

/-! Actual class maps, guarded finite towers, and permutable joins. All
finite instances are obtained before any natural-cardinality inequality. -/

universe u v w t
namespace CCO.FinitePackets.Geometry
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}

theorem finiteIndex_trans (J K L : ColourEq S i) (hJK : J ≤ K) (hKL : K ≤ L)
    (hJ : FiniteIndex S J K) (hK : FiniteIndex S K L) : FiniteIndex S J L := by
  classical
  intro x
  letI := hK x
  letI : Fintype (RelativeClass K.val L.val x) := Fintype.ofFinite _
  let f := relativeCoarsening J.val K.val L.val hJK x
  have hfib (q : RelativeClass K.val L.val x) :
      Finite {p : RelativeClass J.val L.val x // f p = q} := by
    refine Quotient.inductionOn q ?_
    intro y
    letI := hJ y.val
    exact Finite.of_equiv (RelativeClass J.val K.val y.val)
      (relativeFibreEquiv J.val K.val L.val hJK hKL x y)
  letI : ∀ q : RelativeClass K.val L.val x,
      Fintype {p : RelativeClass J.val L.val x // f p = q} := fun q => by
    letI := hfib q
    exact Fintype.ofFinite _
  exact Finite.of_equiv _ (Equiv.sigmaFiberEquiv f)

/-- Restriction forgets the extra E-condition on representatives and keeps
the ACTUAL J-class. E is automatic between two source representatives. -/
def restrictionClassMap {A : Type v} (E J K : Setoid A) (x : A) :
    RelativeClass (E ⊓ J) (E ⊓ K) x → RelativeClass J K x :=
  Quotient.map (fun y => ⟨y.val, y.property.2⟩) (fun _ _ h => h.2)

theorem restrictionClassMap_injective {A : Type v} (E J K : Setoid A) (x : A) :
    Function.Injective (restrictionClassMap E J K x) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro y z h
  change Quotient.mk (Setoid.comap (fun p : {p // K x p} => p.val) J)
    ⟨y.val, y.property.2⟩ = Quotient.mk _ ⟨z.val, z.property.2⟩ at h
  have hJ := Quotient.exact h
  change J y.val z.val at hJ
  apply Quotient.sound
  exact ⟨E.trans (E.symm y.property.1) z.property.1, hJ⟩

theorem finiteIndex_restrict (E J K : ColourEq S i) (h : FiniteIndex S J K) :
    FiniteIndex S (E ⊓ J) (E ⊓ K) := by
  intro x
  letI := h x
  exact Finite.of_injective _ (restrictionClassMap_injective E.val J.val K.val x)

theorem relativeIndex_restrict_le (E J K : ColourEq S i) (x : X i)
    [Finite (RelativeClass J.val K.val x)] :
    relativeIndex (E ⊓ J).val (E ⊓ K).val x ≤ relativeIndex J.val K.val x :=
  Nat.card_le_card_of_injective _ (restrictionClassMap_injective E.val J.val K.val x)

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)

noncomputable def classTransposition (E F : ColourEq S i) (x : X i) :
    RelativeClass (E ⊓ F).val F.val x ≃
      RelativeClass E.val (ColourEq.join S H E F).val x := by
  apply relativeClassTransposition E.val F.val
  intro a b
  rw [sup_comm]
  exact sup_relation_iff S H F E a b

theorem relativeIndex_transposition_colour (E F : ColourEq S i) (x : X i) :
    relativeIndex (E ⊓ F).val F.val x =
      relativeIndex E.val (ColourEq.join S H E F).val x :=
  Nat.card_congr (classTransposition S H E F x)

theorem finiteIndex_join (J K L : ColourEq S i) (hJK : J ≤ K) (hJL : J ≤ L)
    (hK : FiniteIndex S J K) (hL : FiniteIndex S J L) :
    FiniteIndex S J (ColourEq.join S H K L) := by
  letI := ColourEq.lattice S H (i := i)
  have hm : J ≤ K ⊓ L := le_inf hJK hJL
  have hr : FiniteIndex S (K ⊓ L) L := finiteIndex_upper S hm hL
  have hs : FiniteIndex S K (K ⊔ L) := by
    intro x
    letI := hr x
    exact Finite.of_equiv (RelativeClass (K ⊓ L).val L.val x)
      (classTransposition S H K L x)
  exact finiteIndex_trans S J K (K ⊔ L) hJK le_sup_left hK hs

theorem relativeIndex_join_le_product (J K L : ColourEq S i)
    (hJK : J ≤ K) (hJL : J ≤ L) (hK : FiniteIndex S J K)
    (hL : FiniteIndex S J L) (x : X i) :
    relativeIndex J.val (ColourEq.join S H K L).val x ≤
      relativeIndex J.val K.val x * relativeIndex J.val L.val x := by
  letI := ColourEq.lattice S H (i := i)
  letI := finiteIndex_join S H J K L hJK hJL hK hL x
  letI := hL x
  have hm : J ≤ K ⊓ L := le_inf hJK hJL
  have hc : relativeIndex K.val (K ⊔ L).val x ≤ relativeIndex J.val L.val x := by
    calc
      _ = relativeIndex (K ⊓ L).val L.val x :=
        (relativeIndex_transposition_colour S H K L x).symm
      _ ≤ _ := Nat.card_le_card_of_surjective _
        (relativeCoarsening_surjective J.val (K ⊓ L).val L.val hm x)
  rw [relativeIndex_mul S H J K (ColourEq.join S H K L) hJK
    (show K ≤ ColourEq.join S H K L from le_sup_left) x]
  exact Nat.mul_le_mul_left _ hc

/-- The actual transposition bijection across ANY E, after adjoining J.
Its domain is the quotient inside the ORIGINAL K-class, not an interval
order isomorphism or an inferred natural-cardinality equality. -/
noncomputable def indexCrossingEquiv (E J K : ColourEq S i) (hJK : J ≤ K)
    (x : X i) :
    RelativeClass (K ⊓ ColourEq.join S H E J).val K.val x ≃
      RelativeClass (ColourEq.join S H E J).val (ColourEq.join S H E K).val x := by
  letI := ColourEq.lattice S H (i := i)
  have hs : (E ⊔ J) ⊔ K = E ⊔ K := by rw [sup_assoc, sup_eq_right.mpr hJK]
  let e := classTransposition S H (E ⊔ J) K x
  change RelativeClass ((E ⊔ J) ⊓ K).val K.val x ≃
    RelativeClass (E ⊔ J).val ((E ⊔ J) ⊔ K).val x at e
  rw [inf_comm (E ⊔ J) K, hs] at e
  exact e

theorem finiteIndex_join_crossing (E J K : ColourEq S i) (hJK : J ≤ K)
    (hfin : FiniteIndex S J K) :
    FiniteIndex S (ColourEq.join S H E J) (ColourEq.join S H E K) := by
  letI := ColourEq.lattice S H (i := i)
  intro x
  letI := hfin x
  have hJD : J ≤ K ⊓ ColourEq.join S H E J := le_inf hJK le_sup_right
  letI : Finite (RelativeClass (K ⊓ ColourEq.join S H E J).val K.val x) :=
    finite_relative_right J.val _ K.val hJD x
  exact Finite.of_equiv _ (indexCrossingEquiv S H E J K hJK x)

/-- The inner tower factor is identified by an ACTUAL class transposition
and the full modular identity; E need not be a minimal infinite cut. -/
theorem relativeIndex_meet_reroute (E J K : ColourEq S i) (hJK : J ≤ K) (x : X i) :
    relativeIndex J.val (K ⊓ ColourEq.join S H E J).val x =
      relativeIndex (E ⊓ J).val (E ⊓ K).val x := by
  letI := ColourEq.lattice S H (i := i)
  letI : IsModularLattice (ColourEq S i) := ColourEq.modular S H
  have hD : K ⊓ (E ⊔ J) = J ⊔ (E ⊓ K) := by
    calc
      _ = K ⊓ E ⊔ J := (inf_sup_assoc_of_le E hJK).symm
      _ = _ := by rw [inf_comm K E, sup_comm]
  have hm : J ⊓ (E ⊓ K) = E ⊓ J := by
    rw [← inf_assoc, inf_comm J E, inf_assoc, inf_eq_left.mpr hJK]
  have ht := relativeIndex_transposition_colour S H J (E ⊓ K) x
  change relativeIndex (J ⊓ (E ⊓ K)).val (E ⊓ K).val x =
    relativeIndex J.val (J ⊔ (E ⊓ K)).val x at ht
  rw [hm, ← hD] at ht
  exact ht.symm

theorem relativeIndex_factorization (E J K : ColourEq S i) (hJK : J ≤ K)
    (hfin : FiniteIndex S J K) (x : X i) :
    relativeIndex J.val K.val x =
      relativeIndex (ColourEq.join S H E J).val (ColourEq.join S H E K).val x *
        relativeIndex (E ⊓ J).val (E ⊓ K).val x := by
  letI := ColourEq.lattice S H (i := i)
  let D : ColourEq S i := K ⊓ ColourEq.join S H E J
  have hJD : J ≤ D := le_inf hJK le_sup_right
  have hDK : D ≤ K := inf_le_left
  letI := hfin x
  have hm : relativeIndex J.val D.val x =
      relativeIndex (E ⊓ J).val (E ⊓ K).val x :=
    relativeIndex_meet_reroute S H E J K hJK x
  have hc : relativeIndex D.val K.val x =
      relativeIndex (ColourEq.join S H E J).val (ColourEq.join S H E K).val x :=
    Nat.card_congr (indexCrossingEquiv S H E J K hJK x)
  calc
    _ = relativeIndex J.val D.val x * relativeIndex D.val K.val x :=
      relativeIndex_mul S H J D K hJD hDK x
    _ = relativeIndex (E ⊓ J).val (E ⊓ K).val x *
        relativeIndex (ColourEq.join S H E J).val (ColourEq.join S H E K).val x := by
      rw [hm, hc]
    _ = _ := Nat.mul_comm _ _

end CCO.FinitePackets.Geometry
