import CCO.TerminalLattice.FullCoverParity
import CCO.ParityHasse.Original.RelativeIndices

/-!
# B050 C15: elementary TWO-class cardinality and full quotient orbital

The [K:J]=2 case is the actual finite relative-index statement on
original real points, not a hypothetical two-vertex quotient graph.
The FULL old G-quotient orbital then contains EVERY external pair in a
K/J-class: the two distinct J-classes have only each other as neighbors.

This is the first original source boundary for the alternating-power
branch; no CCO, SAP, NR2, exactness or finite quotient carrier.
-/

universe u v w t

namespace CCO.TerminalLattice

/-- Any two distinct points of a type of cardinal exactly two exhaust
that entire type. We use the actual `Nat.card` API, with no finite
enumeration oracle or extra predicate assumptions. -/
theorem two_points_exhaust {Q : Type u}
    (hcard : Nat.card Q = 2) (a b : Q) (hab : a ≠ b) :
    ∀ q : Q, q = a ∨ q = b := by
  classical
  obtain ⟨u, v, huv, hall⟩ := Nat.card_eq_two_iff.mp hcard
  have hfull (q : Q) : q = u ∨ q = v := by
    have h : q ∈ (Set.univ : Set Q) := Set.mem_univ q
    rw [← hall] at h
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  rcases hfull a with ha | ha
  · rcases hfull b with hb | hb
    · exact False.elim (hab (ha.trans hb.symm))
    · intro q
      rcases hfull q with hq | hq
      · exact Or.inl (hq.trans ha.symm)
      · exact Or.inr (hq.trans hb.symm)
  · rcases hfull b with hb | hb
    · intro q
      rcases hfull q with hq | hq
      · exact Or.inr (hq.trans hb.symm)
      · exact Or.inl (hq.trans ha.symm)
    · exact False.elim (hab (ha.trans hb.symm))

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Exactly two old J-classes in K[a], with a,b as actual original
representatives. This is the converse index-two input needed for the
SOURCE C15 alternating branch. No global two-sheet hypothesis occurs. -/
theorem original_index_two_class_decomposition
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (htwo : relativeIndex J.val K.val a = 2) :
    ∀ x : X i, K a x ↔ J a x ∨ J b x := by
  let Q := RelativeClass J.val K.val a
  let qa : Q := Quotient.mk _ ⟨a, K.val.refl a⟩
  let qb : Q := Quotient.mk _ ⟨b, hab⟩
  have habQ : qa ≠ qb := by
    intro hh
    change Quotient.mk _ (⟨a, K.val.refl a⟩ : {x // K a x}) =
      Quotient.mk _ (⟨b, hab⟩ : {x // K a x}) at hh
    have hJ := Quotient.exact hh
    exact hne hJ
  have hCover := two_points_exhaust htwo qa qb habQ
  intro x
  constructor
  · intro hK
    let qx : Q := Quotient.mk _ ⟨x, hK⟩
    rcases hCover qx with h | h
    · change Quotient.mk _ (⟨x, hK⟩ : {z // K a z}) =
        Quotient.mk _ (⟨a, K.val.refl a⟩ : {z // K a z}) at h
      have hJ := Quotient.exact h
      exact Or.inl (J.val.symm hJ)
    · change Quotient.mk _ (⟨x, hK⟩ : {z // K a z}) =
        Quotient.mk _ (⟨b, hab⟩ : {z // K a z}) at h
      have hJ := Quotient.exact h
      exact Or.inr (J.val.symm hJ)
  · rintro (hJ | hJ)
    · exact hJK hJ
    · exact K.val.trans hab (hJK hJ)

/-- In a genuine [K:J]=2 full-cover component there is ONE other
quotient vertex. Two distinct J-classes in the same K-class must be
that same external vertex. -/
theorem original_index_two_unique_external
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (hJK : J ≤ K)
    (a : X i) (htwo : relativeIndex J.val K.val a = 2)
    (x : X i)
    (hKax : K a x) (hnex : ¬ J a x)
    (y : X i)
    (hKay : K a y) (hney : ¬ J a y) :
    J x y := by
  have hCover :=
    original_index_two_class_decomposition S J K hJK a x hKax hnex htwo
  rcases (hCover y).mp hKay with hJ | hJ
  · exact False.elim (hney hJ)
  · exact hJ

/-- SOURCE C15 quotient graph: in actual index two, the one complete
external quotient orbital is literally ALL external pairs of K/J.
The proof only uses original G transitivity to move the initial
old root pair and the actual relative two-class decomposition. -/
theorem originalQuotientOrbital_index_two_external
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (hJK : J ⋖ K)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (htwo : relativeIndex J.val K.val a = 2) :
    originalQuotientOrbital S (G := G) J a b =
      (fun q r : Quotient J.val =>
        originalUpperSetoid S J K hJK.le q r ∧ q ≠ r) := by
  funext q r
  apply propext
  constructor
  · intro horb
    constructor
    · exact originalQuotientOrbital_le_upper
        S H J K hJK.le a b hab q r horb
    · intro heq
      subst r
      exact (originalQuotientOrbital_irreflexive S H J a b hne q) horb
  · rintro ⟨hupper, hneq⟩
    induction q using Quotient.inductionOn with
    | _ x =>
      induction r using Quotient.inductionOn with
      | _ z =>
        obtain ⟨g, hga⟩ :=
          S.original_sort_transitive_of_homogeneous H i a x
        let y : X i := g • b
        have hKxy : K x y := by
          have hk := colourInvariant_groupInvariant S H K.2 g a b hab
          simpa only [hga, y] using hk
        have hJxy : ¬ J x y := by
          intro hJ
          have h : J (g • a) (g • b) := by
            simpa only [hga, y] using hJ
          have hh := colourInvariant_groupInvariant S H J.2
            g⁻¹ (g • a) (g • b) h
          exact hne (by simpa only [inv_smul_smul] using hh)
        have hIdxX : relativeIndex J.val K.val x = 2 :=
          (relativeIndex_uniform S H J K x a).trans htwo
        have hKxz : K x z :=
          (originalUpperSetoid_mk S J K hJK.le x z).mp hupper
        have hJxz : ¬ J x z := by
          intro hh
          exact hneq (Quotient.sound hh)
        have hyz : J y z :=
          original_index_two_unique_external
            S H J K hJK.le x hIdxX y hKxy hJxy z hKxz hJxz
        have hOrb : originalQuotientOrbital S (G := G) J a b
            (Quotient.mk J.val x) (Quotient.mk J.val y) :=
          ⟨g, by simpa only [hga], rfl⟩
        have hyzQ : Quotient.mk J.val y = Quotient.mk J.val z :=
          Quotient.sound hyz
        rw [← hyzQ]
        exact hOrb

end CCO.TerminalLattice
