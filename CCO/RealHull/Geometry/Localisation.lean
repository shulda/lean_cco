import CCO.RealHull.Geometry.Collapse
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-!
# Original support square avoidance and spoke-square localisation

Every product below retains logical equality. Square avoidance is valid for
ANY blocker family; minimality is used only when choosing an outside witness
after a row is removed in the localisation argument.
-/
universe v w t
namespace CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def squareMeet (B : Finset (Atom S)) : Set (Atom S) :=
  {x | ∀ b ∈ B, x ∈ square S b}

theorem prod_choose_right {A B C : Set (FullColour S)} {c : FullColour S}
    (hc : c ∈ prod S A (prod S B C)) :
    ∃ d ∈ prod S B C, c ∈ prod S A {d} := by
  obtain ⟨x,y,z,hA,hBC,hc⟩ := hc
  exact ⟨col S y z,hBC,x,y,z,hA,rfl,hc⟩

variable {G : Type t} [Group G] [MulAction G M] [DecidableEq (Atom S)]

/-- C08, with no unnecessary minimality premise. In particular it applies to
the source's inclusion-minimal blocker. -/
theorem blocker_square_avoidance (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (R : Support S) (B : Finset (Atom S))
    (hcover : squareMeet S B ⊆ R.val) {p : Atom S} (hp : p ∈ B)
    (hfix : Fixed S R p) (a : Atom S) (ha : a ∈ square S p) :
    Disjoint (square S a) (squareMeet S (B.erase p) \ R.val) := by
  classical
  apply Set.disjoint_left.mpr
  intro x hxA hxSi
  have hxR : x ∉ R.val := hxSi.2
  have hxRest : ∀ b ∈ B.erase p, x ∈ square S b := hxSi.1
  have hxNotp : x ∉ square S p := by
    intro hxp
    apply hxR
    apply hcover
    intro b hb
    by_cases he : b = p
    · simpa only [he] using hxp
    · exact hxRest b (Finset.mem_erase.mpr ⟨he,hb⟩)
  have haSub : ({some a} : Set (FullColour S)) ⊆ prod S {some p} {some p} := by
    intro c hc
    exact Set.mem_singleton_iff.mp hc ▸ ha
  have hxx := prod_mono S haSub (Set.Subset.rfl : ({some a} : Set (FullColour S)) ⊆ _) hxA
  rw [prod_assoc S H] at hxx
  obtain ⟨d,hd,hxp⟩ := prod_choose_right S hxx
  cases d with
  | none =>
    have hpa : p = a := (none_mem_atom_prod S p a).mp hd
    rw [prod_none_right] at hxp
    have hxeq : x = p := Option.some.inj (Set.mem_singleton_iff.mp hxp)
    exact hxNotp (by simpa only [hpa] using hxA)
  | some d =>
    by_cases hdp : d = p
    · subst d
      exact hxNotp hxp
    have hda : some a ∈ prod S {some d} {some p} :=
      (optional_peirce S (some a) (some d) (some p)).mp
        ((optional_peirce S (some p) (some a) (some d)).mp hd)
    by_cases hdR : d ∈ R.val
    · have hsub : ({some d} : Set (FullColour S)) ⊆ plus S R.val := by
        intro c hc
        exact Set.mem_singleton_iff.mp hc ▸ (some_mem_plus S _ _).mpr hdR
      have hh := prod_mono S hsub Set.Subset.rfl hda
      rw [hfix] at hh
      have hap : a = p := Option.some.inj (Set.mem_singleton_iff.mp hh)
      exact hxNotp (by simpa only [hap] using hxA)
    have had : a ∈ row S p d := by
      change some a ∈ prod S {some p} {some d}
      rw [prod_comm]
      exact hda
    have horbit : SupportOrbit S R p d := by
      by_contra hnot
      obtain ⟨b,hb,hsep⟩ := relative_separator S H cco R B hcover p d hnot
      have hmeet : (row S b p ∩ row S b d).Nonempty := by
        by_cases hbp : b = p
        · subst b
          exact ⟨a,ha,had⟩
        · apply (rectangle S H b p d (Ne.symm hdp)).mpr
          exact ⟨x,hxRest b (Finset.mem_erase.mpr ⟨hbp,hb⟩),hxp⟩
      exact Set.disjoint_left.mp hsep hmeet.choose_spec.1 hmeet.choose_spec.2
    exact hdp ((fixed_orbit S hfix d).mp horbit)

/-- C12. The chosen blocker is inclusion-minimal by minimum cardinality. Its
equality row is the ORIGINAL square of `c`, not a synthetic strong identity.
-/
theorem spoke_square_localisation (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (R : Support S) (P : Finset (Atom S))
    (_hP : P.Nonempty) (hfix : ∀ p ∈ P, Fixed S R p) (c : Atom S)
    (hc : c ∈ squareMeet S P) (hcover : square S c ∩ squareMeet S P ⊆ R.val) :
    square S c ⊆ R.val ∧ ∀ p ∈ P, prod S {some p} {some c} = {some p} := by
  classical
  have hAc : square S c ⊆ R.val := by
    by_cases hcR : c ∈ R.val
    · intro x hx
      have hsub : ({some c} : Set (FullColour S)) ⊆ plus S R.val := by
        intro d hd
        exact Set.mem_singleton_iff.mp hd ▸ (some_mem_plus S _ _).mpr hcR
      exact (some_mem_plus S _ _).mp (R.property (prod_mono S hsub hsub hx))
    · let B0 := insert c P
      have hB0 : squareMeet S B0 ⊆ R.val := by
        intro x hx
        exact hcover ⟨hx c (Finset.mem_insert_self _ _),
          fun p hp => hx p (Finset.mem_insert_of_mem hp)⟩
      have hex : ∃ n : Nat, ∃ B : Finset (Atom S),
          B ⊆ B0 ∧ squareMeet S B ⊆ R.val ∧ B.card = n :=
        ⟨B0.card,B0,Finset.Subset.refl _,hB0,rfl⟩
      obtain ⟨B,hBsub,hB,hcard⟩ := Nat.find_spec hex
      have hmin (p : Atom S) (hp : p ∈ B) : ¬ squareMeet S (B.erase p) ⊆ R.val := by
        intro he
        have hsmall : (B.erase p).card < Nat.find hex := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem hp
        exact Nat.find_min hex hsmall ⟨B.erase p,
          fun b hb => hBsub (Finset.mem_of_mem_erase hb),he,rfl⟩
      have hcB : c ∈ B := by
        by_contra hn
        apply hcR
        apply hB
        intro b hb
        have hbP : b ∈ P := by
          rcases Finset.mem_insert.mp (hBsub hb) with he | he
          · exact False.elim (hn (he ▸ hb))
          · exact he
        exact hc b hbP
      by_cases hOnly : B ⊆ {c}
      · intro x hx
        apply hB
        intro b hb
        have he : b = c := Finset.mem_singleton.mp (hOnly hb)
        simpa only [he] using hx
      · obtain ⟨p,hp,hpc⟩ := Finset.not_subset.mp hOnly
        have hpne : p ≠ c := by simpa only [Finset.mem_singleton] using hpc
        have hpP : p ∈ P := (Finset.mem_insert.mp (hBsub hp)).resolve_left hpne
        have hxExists : ∃ x, x ∈ squareMeet S (B.erase p) ∧ x ∉ R.val := by
          by_contra hn
          apply hmin p hp
          intro x hx
          by_contra hxR
          exact hn ⟨x,hx,hxR⟩
        obtain ⟨x,hx,hxR⟩ := hxExists
        have hxAc : x ∈ square S c := hx c (Finset.mem_erase.mpr ⟨Ne.symm hpne,hcB⟩)
        have hdisj := blocker_square_avoidance S H cco R B hB hp (hfix p hpP) c (hc p hpP)
        exact False.elim (Set.disjoint_left.mp hdisj hxAc ⟨hx,hxR⟩)
  refine ⟨hAc,fun p hp => ?_⟩
  exact (self_side_collapse S H cco R (hfix p hp) (hc p hp)
    (fun _ hx => hAc hx.1)).1

end CCO.RealHull.Geometry
