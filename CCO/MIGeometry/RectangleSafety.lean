import CCO.MIGeometry.ComplementarySpectrum
import CCO.MIGeometry.GroupAmalgamation

/-! Full-support descent for an owner-complete closed padded span. The
original amalgam fixes a full base rectangle. Its complementary coordinates
are consequently anchored pointwise before any fine colours are read out. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds AclOwners
open RawExact ExactCRT FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (C K : ColourEq S ())

/-- A quotient diversity colour is safe when EVERY original fine lift is
in the given original palette. Equality is outside this palette. -/
def fullSupportPalette (safe : Set (Atom S)) :
    Set (Atom (actualQuotientSource S H C)) :=
  {q | ∀ u v : M, col (actualQuotientSource S H C) (Quotient.mk'' u) (Quotient.mk'' v) = some q →
    ∃ a ∈ safe, col S u v = some a}

/-- Unsafe old pairs stay unsafe whenever projected as a diversity pair.
The equality-inclusive conclusion also covers coincident quotient images. -/
theorem fullSupportPalette_unsafe (safe : Set (Atom S)) (x y : M)
    (hunsafe : ¬ ∃ a ∈ safe, col S x y = some a) :
    ¬ ∃ q ∈ fullSupportPalette S H C safe,
      col (actualQuotientSource S H C) (Quotient.mk'' x) (Quotient.mk'' y) = some q := by
  rintro ⟨q,hq,hcol⟩
  exact hunsafe (hq x y hcol)

noncomputable def exactRectangle (hCK : C.val ⊓ K.val = ⊥)
    (D : Finset (Quotient C.val)) (P : Finset (Quotient K.val)) : Finset M :=
  (rectangleSet_finite S C K hCK D P).toFinset

@[simp] theorem mem_exactRectangle (hCK : C.val ⊓ K.val = ⊥)
    (D : Finset (Quotient C.val)) (P : Finset (Quotient K.val)) (x : M) :
    x ∈ exactRectangle S C K hCK D P ↔
      (Quotient.mk'' x : Quotient C.val) ∈ D ∧ (Quotient.mk'' x : Quotient K.val) ∈ P :=
  (rectangleSet_finite S C K hCK D P).mem_toFinset

include H in
/-- Actual CRT supplies a vertex above every compatible pair. -/
theorem rectangle_point (hCK : C.val ⊓ K.val = ⊥)
    (y : Quotient C.val) (p : Quotient K.val)
    (compatible : Abstract.quotientMap (show C.val ≤ C.val ⊔ K.val from le_sup_left) y =
      Abstract.quotientMap (show K.val ≤ C.val ⊔ K.val from le_sup_right) p) :
    ∃ x : M, (Quotient.mk'' x : Quotient C.val) = y ∧
      (Quotient.mk'' x : Quotient K.val) = p := by
  let a : Abstract.FibreProduct C.val K.val := ⟨(y,p),compatible⟩
  let x := (realFibreProductEquiv S H C K hCK).symm a
  have hx := congrArg Subtype.val ((realFibreProductEquiv S H C K hCK).apply_symm_apply a)
  exact ⟨x,congrArg Prod.fst hx,congrArg Prod.snd hx⟩

variable [Countable M] (cco : SemanticCCO.{0,v,0,w} S)
variable (BC BK : NonemptyExact S () ())
variable (hC : evaluate S BC.words = C.val.r) (hK : evaluate S BK.words = K.val.r)
include H cco BC BK hC hK

/-- C19: a finite full rectangle is absolutely closed. Both factor
closures are absolute; no owner harmlessness is assumed here. -/
theorem exactRectangle_closed (hCK : C.val ⊓ K.val = ⊥)
    (D : Finset (Quotient C.val)) (P : Finset (Quotient K.val))
    (hne : (rectangleSet S C K D P).Nonempty) :
    letI := originalQuotientAction S H C
    letI := originalQuotientAction S H K
    Closed G D → Closed G P → Closed G (exactRectangle S C K hCK D P) := by
  classical
  letI := originalQuotientAction S H C
  letI := originalQuotientAction S H K
  intro hD hP
  obtain ⟨W,_,hW,closed⟩ := rectangle_absolute_closure S H C K cco hCK BC BK hC hK D P hne hD hP
  have he : W = exactRectangle S C K hCK D P := by
    ext x
    exact (hW x).trans (mem_exactRectangle S C K hCK D P x).symm
  exact he ▸ closed

/-- C19–C22: all projected cross colours have their ENTIRE old support
safe. Common base points force the same actual complementary coordinates
through the original amalgam. -/
theorem padded_full_support_amalgamation (hCK : C.val ⊓ K.val = ⊥)
    (safe : Set (Atom S)) (amalgamate : StrongClosedAmalgamation S G safe)
    (B : Finset (Quotient (C.val ⊔ K.val))) (hB : B.Nonempty)
    (D L R : Finset (Quotient C.val)) (P : Finset (Quotient K.val))
    (hDL : D ⊆ L) (hDR : D ⊆ R)
    (ownersL : ∀ y ∈ L, Abstract.quotientMap (show C.val ≤ C.val ⊔ K.val from le_sup_left) y ∈ B)
    (ownersR : ∀ y ∈ R, Abstract.quotientMap (show C.val ≤ C.val ⊔ K.val from le_sup_left) y ∈ B)
    (ontoD : ∀ b ∈ B, ∃ y ∈ D,
      Abstract.quotientMap (show C.val ≤ C.val ⊔ K.val from le_sup_left) y = b)
    (spectrum : OwnerSpectrum (actualQuotientSource S H K)
      (Abstract.quotientMap (show K.val ≤ C.val ⊔ K.val from le_sup_right)) B P) :
    letI := originalQuotientAction S H C
    letI := originalQuotientAction S H K
    Closed G D → Closed G L → Closed G R → Closed G P →
    ∃ g : G, (∀ d ∈ D, g • d = d) ∧
      (∀ y ∈ L, ∀ z ∈ R, y = g • z ↔ y = z ∧ y ∈ D) ∧
      (∀ y ∈ L, y ∉ D → ∀ z ∈ R, z ∉ D →
        ∃ q ∈ fullSupportPalette S H C safe, col (actualQuotientSource S H C) y (g • z) = some q) := by
  classical
  letI := originalQuotientAction S H C
  letI := originalQuotientAction S H K
  let ownerY := Abstract.quotientMap (show C.val ≤ C.val ⊔ K.val from le_sup_left)
  let ownerX := Abstract.quotientMap (show K.val ≤ C.val ⊔ K.val from le_sup_right)
  intro closedD closedL closedR closedP
  let WD := exactRectangle S C K hCK D P
  let WL := exactRectangle S C K hCK L P
  let WR := exactRectangle S C K hCK R P
  have hWD : Closed G WD := exactRectangle_closed S H C K cco BC BK hC hK hCK D P
    (rectangle_nonempty_of_owner S H C K hCK D P B hB ontoD spectrum.2.1) closedD closedP
  have hWL : Closed G WL := exactRectangle_closed S H C K cco BC BK hC hK hCK L P
    (rectangle_nonempty_of_owner S H C K hCK L P B hB
      (fun b hb => by obtain ⟨y,hy,he⟩ := ontoD b hb; exact ⟨y,hDL hy,he⟩) spectrum.2.1) closedL closedP
  have hWR : Closed G WR := exactRectangle_closed S H C K cco BC BK hC hK hCK R P
    (rectangle_nonempty_of_owner S H C K hCK R P B hB
      (fun b hb => by obtain ⟨y,hy,he⟩ := ontoD b hb; exact ⟨y,hDR hy,he⟩) spectrum.2.1) closedR closedP
  have subL : WD ⊆ WL := fun x hx => (mem_exactRectangle S C K hCK L P x).mpr
    ⟨hDL ((mem_exactRectangle S C K hCK D P x).mp hx).1,
      ((mem_exactRectangle S C K hCK D P x).mp hx).2⟩
  have subR : WD ⊆ WR := fun x hx => (mem_exactRectangle S C K hCK R P x).mpr
    ⟨hDR ((mem_exactRectangle S C K hCK D P x).mp hx).1,
      ((mem_exactRectangle S C K hCK D P x).mp hx).2⟩
  obtain ⟨g,base,strong,cross⟩ := strong_closed_group_amalgamation S H safe amalgamate
    WD WL WR hWD hWL hWR subL subR
  have fixesP : ∀ p ∈ P, g • p = p := by
    intro p hp
    obtain ⟨d,hd,hdo⟩ := ontoD (ownerX p) (spectrum.1 p hp)
    obtain ⟨x,hxC,hxK⟩ := rectangle_point S H C K hCK d p hdo
    have hxD : x ∈ WD := (mem_exactRectangle S C K hCK D P x).mpr ⟨hxC.symm ▸ hd,hxK.symm ▸ hp⟩
    have he := congrArg (Quotient.mk'' : M → Quotient K.val) (base x hxD)
    change g • (Quotient.mk'' x : Quotient K.val) = Quotient.mk'' x at he
    simpa only [hxK] using he
  have fixesD : ∀ d ∈ D, g • d = d := by
    intro d hd
    obtain ⟨p,hp,hpo⟩ := spectrum.2.1 (ownerY d) (ownersL d (hDL hd))
    obtain ⟨x,hxC,hxK⟩ := rectangle_point S H C K hCK d p hpo.symm
    have hxD : x ∈ WD := (mem_exactRectangle S C K hCK D P x).mpr ⟨hxC.symm ▸ hd,hxK.symm ▸ hp⟩
    have he := congrArg (Quotient.mk'' : M → Quotient C.val) (base x hxD)
    change g • (Quotient.mk'' x : Quotient C.val) = Quotient.mk'' x at he
    simpa only [hxC] using he
  have strongY : ∀ y ∈ L, ∀ z ∈ R, y = g • z ↔ y = z ∧ y ∈ D := by
    intro y hy z hz
    constructor
    · intro he
      obtain ⟨p,hp,hpo⟩ := spectrum.2.1 (ownerY z) (ownersR z hz)
      obtain ⟨x,hxC,hxK⟩ := rectangle_point S H C K hCK z p hpo.symm
      have hxR : x ∈ WR := (mem_exactRectangle S C K hCK R P x).mpr ⟨hxC.symm ▸ hz,hxK.symm ▸ hp⟩
      have hgxC : (Quotient.mk'' (g • x) : Quotient C.val) = y := by
        change g • (Quotient.mk'' x : Quotient C.val) = y
        rw [hxC,he]
      have hgxK : (Quotient.mk'' (g • x) : Quotient K.val) = p := by
        change g • (Quotient.mk'' x : Quotient K.val) = p
        rw [hxK,fixesP p hp]
      have hgxL : g • x ∈ WL := (mem_exactRectangle S C K hCK L P (g • x)).mpr
        ⟨hgxC.symm ▸ hy,hgxK.symm ▸ hp⟩
      obtain ⟨he',hbase⟩ := (strong (g • x) hgxL x hxR).mp rfl
      have hyD : y ∈ D := hgxC ▸ ((mem_exactRectangle S C K hCK D P (g • x)).mp hbase).1
      have hyz : y = z := hgxC.symm.trans ((congrArg Quotient.mk'' he').trans hxC)
      exact ⟨hyz,hyD⟩
    · rintro ⟨he,hyD⟩
      rw [← he]
      exact (fixesD y hyD).symm
  refine ⟨g,fixesD,strongY,?_⟩
  intro y hy hyD z hz hzD
  have hne : y ≠ g • z := fun he => hyD ((strongY y hy z hz).mp he).2
  obtain ⟨q,hq⟩ := col_some_of_ne (actualQuotientSource S H C) hne
  refine ⟨q,?_,hq⟩
  intro u v huv
  have ownersGz : ownerY (g • z) ∈ B := by
    obtain ⟨p,hp,hpo⟩ := spectrum.2.1 (ownerY z) (ownersR z hz)
    have he : ownerY (g • z) = ownerX (g • p) := by
      induction z using Quotient.inductionOn with | _ a =>
        induction p using Quotient.inductionOn with | _ b =>
          exact Quotient.sound ((colourInvariant_groupInvariant S H
            (ColourEq.join S H C K).property g a b) (Quotient.exact hpo.symm))
    rw [he,fixesP p hp]
    exact spectrum.1 p hp
  obtain ⟨x,x',hxY,hxY',hxP,hxP',hFine⟩ := complementary_spectrum S H cco C K
    ⟨BC,hC⟩ ⟨BK,hK⟩ hCK B P spectrum y (g • z) (ownersL y hy) ownersGz u v (huv.trans hq.symm)
  have hxL : x ∈ WL := (mem_exactRectangle S C K hCK L P x).mpr ⟨hxY.symm ▸ hy,hxP⟩
  have hxD : x ∉ WD := fun h => hyD (hxY ▸ ((mem_exactRectangle S C K hCK D P x).mp h).1)
  have hinvY : (Quotient.mk'' (g⁻¹ • x') : Quotient C.val) = z := by
    change g⁻¹ • (Quotient.mk'' x' : Quotient C.val) = z
    rw [hxY',inv_smul_smul]
  have hinvK : (Quotient.mk'' (g⁻¹ • x') : Quotient K.val) ∈ P := by
    change g⁻¹ • (Quotient.mk'' x' : Quotient K.val) ∈ P
    have he : g⁻¹ • (Quotient.mk'' x' : Quotient K.val) = Quotient.mk'' x' :=
      (inv_smul_eq_iff).mpr (fixesP _ hxP').symm
    rwa [he]
  have hxR : g⁻¹ • x' ∈ WR := (mem_exactRectangle S C K hCK R P _).mpr ⟨hinvY.symm ▸ hz,hinvK⟩
  have hxD' : g⁻¹ • x' ∉ WD := fun h => hzD (hinvY ▸ ((mem_exactRectangle S C K hCK D P _).mp h).1)
  obtain ⟨a,ha,hca⟩ := cross x hxL hxD (g⁻¹ • x') hxR hxD'
  rw [smul_inv_smul] at hca
  exact ⟨a,ha,hFine.symm.trans hca⟩

end CCO.MIGeometry
