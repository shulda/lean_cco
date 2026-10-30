import CCO.RankInduction.PaletteTransfer

/-! The finite-exact rank branch uses the nonrelative full inverse image
of a supplied lower witness. Closedness is transferred only when that
chosen quotient witness is closed. -/

universe v w t
namespace CCO.RankInduction
noncomputable section
open RawExact ExactCRT Owners.Product Owners.Provider

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (E : ExactEq S H cco ())

def rankKernel : FiniteLift.ExactKernel S G :=
  FiniteLift.ExactKernel.ofExact H E.val (exactPresentation S E.property)
    (exactPresentation_represents S E.property)

local instance restoreQuotientInvariant : CanonicalQuotients.Invariant G E.val :=
  Owners.Product.exactInvariant S H cco E

def descendedPalette (safe : Set (S.Atom () ())) :
    Set ((Owners.Master.quotientSource S H cco E).Atom () ()) :=
  namedPalette (Owners.Master.quotientSource S H cco E)
    (FiniteLift.quotientSafePalette S (rankKernel S H cco E) safe)

theorem descendedPalette_relation (safe : Set (S.Atom () ())) :
    (Owners.Master.quotientSource S H cco E).menuRel (descendedPalette S H cco E safe) =
      FiniteLift.quotientSafePalette S (rankKernel S H cco E) safe := by
  apply menuRel_namedPalette _ (Owners.Master.quotientSource_homogeneous S H cco E)
  · intro q hq
    exact hq.1 rfl
  · intro g x y hxy
    exact (FiniteLift.quotientSafePalette_smul S (rankKernel S H cco E) H safe g x y).mpr hxy

theorem finite_exact_safe_descent (finiteE : (rankKernel S H cco E).FiniteClasses)
    (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe)) :
    FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G)
      ((Owners.Master.quotientSource S H cco E).menuRel (descendedPalette S H cco E safe)) := by
  rw [descendedPalette_relation]
  exact strong_closed_from_full (Owners.Master.quotientSource S H cco E)
    (Owners.Master.quotientSource_homogeneous S H cco E) _
    ((rankKernel S H cco E).strongClosedSafePalette H cco finiteE safe hs)

theorem restore_plain_witness (finiteE : (rankKernel S H cco E).FiniteClasses)
    (safe : Set (S.Atom () ())) (A0 : Set M) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty)
    (D : Set (Quotient E.val))
    (w : Witness (Owners.Master.quotientSource S H cco E) G
      (descendedPalette S H cco E safe) ((Quotient.mk'' : M → Quotient E.val) '' A0) D) :
    Witness S G safe A0 ((Quotient.mk'' : M → Quotient E.val) ⁻¹' D) := by
  let K := rankKernel S H cco E
  have hp : FiniteLift.OrdinaryWitness (G := G) (FiniteLift.aclSet G)
      (FiniteLift.quotientSafePalette S K safe) (K.proj '' A0) D := by
    change FiniteLift.OrdinaryWitness (G := G) (FiniteLift.aclSet G)
      ((Owners.Master.quotientSource S H cco E).menuRel (descendedPalette S H cco E safe))
      (K.proj '' A0) D at w
    rw [descendedPalette_relation] at w
    exact w
  have hc : FiniteLift.aclSet (FiniteLift.FullAut G K.Q) (K.proj '' A0) =
      FiniteLift.aclSet G (K.proj '' A0) :=
    FiniteLift.aclSet_full_eq (K.quotientSource H)
      (K.quotientSource_homogeneous H cco) (K.proj '' A0) (finiteA.image K.proj)
  have hfull : FiniteLift.OrdinaryWitness (G := G)
      (FiniteLift.aclSet (FiniteLift.FullAut G K.Q))
      (FiniteLift.quotientSafePalette S K safe) (K.proj '' A0) D := by
    refine ⟨hp.finite,?_,hp.extensions,?_⟩
    · rw [hc]
      exact hp.closure
    · intro Z hZ z hz
      obtain ⟨α,hα,hz'⟩ := hp.roots Z hZ z hz
      refine ⟨α,?_,hz'⟩
      intro x hx
      rw [hc]
      exact hα x hx
  exact FiniteLift.ordinary_source S H cco K finiteE safe A0 finiteA nonemptyA D hfull

theorem restore_closed_carrier (finiteE : (rankKernel S H cco E).FiniteClasses)
    (D : Set (Quotient E.val)) (finiteD : D.Finite) (closedD : FiniteLift.aclSet G D = D) :
    FiniteLift.aclSet G ((Quotient.mk'' : M → Quotient E.val) ⁻¹' D) =
      (Quotient.mk'' : M → Quotient E.val) ⁻¹' D := by
  apply (rankKernel S H cco E).fullPreimage_closed H cco finiteE D finiteD
  exact (FiniteLift.aclSet_full_eq (Owners.Master.quotientSource S H cco E)
    (Owners.Master.quotientSource_homogeneous S H cco E) D finiteD).trans closedD

theorem finite_exact_plain (proper : E ≠ ⊥)
    (finiteE : (rankKernel S H cco E).FiniteClasses) (lower : Lower S G H cco)
    (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe))
    (A0 : Set M) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty) :
    ∃ W : Set M, Witness S G safe A0 W := by
  obtain ⟨D,hD⟩ := (lower E proper).1 (descendedPalette S H cco E safe)
    (finite_exact_safe_descent S H cco E finiteE safe hs)
    ((Quotient.mk'' : M → Quotient E.val) '' A0)
    (finiteA.image _) (nonemptyA.image _)
  exact ⟨_,restore_plain_witness S H cco E finiteE safe A0 finiteA nonemptyA D hD⟩

theorem finite_exact_closed (proper : E ≠ ⊥)
    (finiteE : (rankKernel S H cco E).FiniteClasses) (lower : LowerClosed S G H cco)
    (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe))
    (A0 : Set M) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty) :
    ∃ W : Set M, Witness S G safe A0 W ∧ FiniteLift.aclSet G W = W := by
  obtain ⟨D,hD,hclosed⟩ := lower E proper (descendedPalette S H cco E safe)
    (finite_exact_safe_descent S H cco E finiteE safe hs)
    ((Quotient.mk'' : M → Quotient E.val) '' A0)
    (finiteA.image _) (nonemptyA.image _)
  exact ⟨_,restore_plain_witness S H cco E finiteE safe A0 finiteA nonemptyA D hD,
    restore_closed_carrier S H cco E finiteE D hD.finite hclosed⟩

end
end CCO.RankInduction
