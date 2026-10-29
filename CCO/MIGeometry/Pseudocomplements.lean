import CCO.AclOwners.CoordinateMeets
import CCO.AclOwners.CoordinateQuotients
import CCO.AclOwners.CorrespondenceUpper
import CCO.ExactCRT.SourceLattice
import Mathlib.Order.Atoms

/-! Maximal exact cores in the ORIGINAL correspondence equivalences.
The old packet core is retained separately.  Only the exact sublattice is
used for the finite join; no distributivity of all invariant equivalences
is asserted. -/

universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact AclOwners

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

abbrev ExactL : Type v := ExactCRT.ExactEq S H (semanticCCO_change_universe S cco) ()

instance exactLFinite : Finite (ExactL S H cco) :=
  ExactCRT.exactEqFinite S H (semanticCCO_change_universe S cco) ()
instance exactLOrderBot : OrderBot (ExactL S H cco) :=
  ExactCRT.exactEqOrderBot S H (semanticCCO_change_universe S cco) ()
instance exactLOrderTop : OrderTop (ExactL S H cco) :=
  ExactCRT.exactEqOrderTop S H (semanticCCO_change_universe S cco) ()

/-- An exact equivalence as an actual colour-invariant equivalence. -/
def exactColour (E : ExactL S H cco) : ColourEq S () :=
  ⟨E.val, ExactCRT.isExactEq_colourInvariant S H E.property⟩

@[simp] theorem exactColour_le (E F : ExactL S H cco) :
    exactColour S H cco E ≤ exactColour S H cco F ↔ E ≤ F := Iff.rfl

/-- The equivalence hypothesis is explicit: exact arbitrary binary relations
cannot be substituted in this criterion. -/
theorem exact_le_correspondence_iff (normalized : NoFiniteExactKernel S)
    (D : Direction S) (E : ColourEq S ()) (hE : ExactCRT.IsExactEq S (i := ()) E.val) :
    E ≤ oldCorrespondence S H cco D ↔ E ⊓ D.val = ⊥ := by
  constructor
  · intro hER
    apply normalized_exact_finite S normalized _
      (ExactCRT.isExactEq_inf S hE (direction_exact S H cco D))
    apply finiteClasses_of_le S (F := finitePacket S H) ?_ (finitePacket_finite S H)
    intro x y hxy
    exact ((correspondence_inf_eq_packet S H cco normalized D.val).mp
      ⟨hxy.2,hER hxy.1⟩).2
  · intro hED
    exact disjoint_le_correspondence S D.val E (inf_comm E D.val ▸ hED)

/-- Join of ALL actual exact equivalences below the correspondence. -/
noncomputable def hatExact (D : Direction S) : ExactL S H cco := by
  classical
  letI : Fintype (ExactL S H cco) := Fintype.ofFinite _
  exact (Finset.univ.filter (fun E => exactColour S H cco E ≤ oldCorrespondence S H cco D)).sup id

noncomputable def hat (D : Direction S) : ColourEq S () :=
  exactColour S H cco (hatExact S H cco D)

theorem hat_exact (D : Direction S) : ExactCRT.IsExactEq S (i := ()) (hat S H cco D).val :=
  (hatExact S H cco D).property

/-- Every join in the exact sublattice is the ambient equivalence join. -/
theorem hat_le_correspondence (D : Direction S) :
    hat S H cco D ≤ oldCorrespondence S H cco D := by
  classical
  letI : Fintype (ExactL S H cco) := Fintype.ofFinite _
  have aux (s : Finset (ExactL S H cco))
      (hs : ∀ E ∈ s, exactColour S H cco E ≤ oldCorrespondence S H cco D) :
      (s.sup id).val ≤ (oldCorrespondence S H cco D).val := by
    induction s using Finset.induction_on with
    | empty => exact bot_le
    | @insert e s hne ih =>
      rw [Finset.sup_insert]
      change e.val ⊔ (s.sup id).val ≤ _
      exact sup_le (hs e (by simp)) (ih (fun E hE => hs E (by simp [hE])))
  exact aux _ (fun E hE => (Finset.mem_filter.mp hE).2)

theorem le_hat (D : Direction S) (E : ColourEq S ())
    (hE : ExactCRT.IsExactEq S (i := ()) E.val) (hle : E ≤ oldCorrespondence S H cco D) :
    E ≤ hat S H cco D := by
  classical
  letI : Fintype (ExactL S H cco) := Fintype.ofFinite _
  let e : ExactL S H cco := ⟨E.val,hE⟩
  exact (Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ e,hle⟩) :
    e ≤ (Finset.univ.filter (fun E => exactColour S H cco E ≤ oldCorrespondence S H cco D)).sup id)

theorem le_hat_iff (normalized : NoFiniteExactKernel S)
    (D : Direction S) (E : ColourEq S ()) (hE : ExactCRT.IsExactEq S (i := ()) E.val) :
    E ≤ hat S H cco D ↔ E ⊓ D.val = ⊥ := by
  constructor
  · intro h
    exact (exact_le_correspondence_iff S H cco normalized D E hE).mp
      (h.trans (hat_le_correspondence S H cco D))
  · intro h
    exact le_hat S H cco D E hE
      ((exact_le_correspondence_iff S H cco normalized D E hE).mpr h)

theorem hat_disjoint (normalized : NoFiniteExactKernel S) (D : Direction S) :
    hat S H cco D ⊓ D.val = ⊥ :=
  (le_hat_iff S H cco normalized D _ (hat_exact S H cco D)).mp le_rfl

theorem oldCore_le_hat (D : Direction S) :
    oldCore S H cco D ≤ hat S H cco D :=
  le_hat S H cco D _ (core_exact S H _) (core_le S _)

theorem direction_le_hat_other (normalized : NoFiniteExactKernel S)
    (D E : Direction S) (hne : D ≠ E) : E.val ≤ hat S H cco D :=
  le_hat S H cco D E.val (direction_exact S H cco E)
    (direction_le_other_correspondence S H cco normalized D E hne)

/-- In a normalized source a minimal infinite direction is an exact atom. -/
theorem direction_exact_atom (normalized : NoFiniteExactKernel S) (D : Direction S) :
    IsAtom (show ExactL S H cco from ⟨D.val.val,direction_exact S H cco D⟩) := by
  refine ⟨?_,?_⟩
  · intro h
    have he : D.val = ⊥ := Subtype.ext (congrArg (fun z : ExactL S H cco => z.val) h)
    exact D.property.1 (he ▸ finiteClasses_bot S)
  · intro e he
    have hle : exactColour S H cco e ≤ D.val := he.le
    have hne : exactColour S H cco e ≠ D.val := by
      intro h
      exact he.ne (Subtype.ext (congrArg (fun z : ColourEq S () => z.val) h))
    have hfin := D.property.2 _ (lt_of_le_of_ne hle hne)
    have hz := normalized_exact_finite S normalized (exactColour S H cco e) e.property hfin
    exact Subtype.ext (congrArg (fun z : ColourEq S () => z.val) hz)

/-- The converse uses ALL invariant subequivalences: every infinite one
contains an original minimal infinite direction, already proved exact. -/
theorem exact_atom_isDirection (normalized : NoFiniteExactKernel S)
    (E : ExactL S H cco) (hE : IsAtom E) : IsDirection S (exactColour S H cco E) := by
  refine ⟨?_,?_⟩
  · intro hfin
    have hz := normalized_exact_finite S normalized (exactColour S H cco E) E.property hfin
    exact hE.ne_bot (Subtype.ext (congrArg (fun z : ColourEq S () => z.val) hz))
  · intro F hF
    by_contra hfin
    obtain ⟨D,hDF⟩ := exists_direction_le S hfin
    let d : ExactL S H cco := ⟨D.val.val,direction_exact S H cco D⟩
    have hdE : d ≤ E := hDF.trans hF.le
    have hdne : d ≠ ⊥ := (direction_exact_atom S H cco normalized D).ne_bot
    have hEd : E ≤ d := by
      by_contra hn
      exact hdne (hE.2 d (lt_of_le_of_ne hdE (fun he => hn he.ge)))
    exact hF.not_ge (fun _ _ h => hDF (hEd h))

/-- No identification of the FULL invariant lattice with the exact lattice
is assumed in the normalized atom/direction bridge. -/
theorem isDirection_iff_exact_atom (normalized : NoFiniteExactKernel S)
    (E : ExactL S H cco) :
    IsDirection S (exactColour S H cco E) ↔ IsAtom E := by
  constructor
  · intro h
    have ha := direction_exact_atom S H cco normalized ⟨exactColour S H cco E,h⟩
    exact ha
  · exact exact_atom_isDirection S H cco normalized E

noncomputable def allHat : ColourEq S () := colourFamilyMeet S (hat S H cco)

theorem allHat_exact : ExactCRT.IsExactEq S (i := ()) (allHat S H cco).val :=
  colourFamilyMeet_exact S _ (hat_exact S H cco)

/-- The exhaustive original direction index is essential here. -/
theorem allHat_eq_bot (normalized : NoFiniteExactKernel S) : allHat S H cco = ⊥ := by
  apply normalized_exact_finite S normalized _ (allHat_exact S H cco)
  apply finiteClasses_of_le S (F := finitePacket S H) ?_ (finitePacket_finite S H)
  rw [← allCorrespondence_eq_packet S H cco normalized]
  intro x y hxy D
  exact hat_le_correspondence S H cco D (hxy D)

theorem hat_infinite_of_other (normalized : NoFiniteExactKernel S)
    (D E : Direction S) (hne : D ≠ E) : ¬ FiniteClasses S (hat S H cco D) := by
  intro hf
  exact E.property.1 (finiteClasses_of_le S (direction_le_hat_other S H cco normalized D E hne) hf)

theorem hat_ne_bot_of_other (normalized : NoFiniteExactKernel S)
    (D E : Direction S) (hne : D ≠ E) : hat S H cco D ≠ ⊥ := by
  intro h
  exact hat_infinite_of_other S H cco normalized D E hne (h ▸ finiteClasses_bot S)

theorem hat_ne_top (normalized : NoFiniteExactKernel S) (D : Direction S) :
    hat S H cco D ≠ ⊤ := by
  intro h
  have hd := hat_disjoint S H cco normalized D
  rw [h,top_inf_eq] at hd
  exact D.property.1 (hd ▸ finiteClasses_bot S)

end CCO.MIGeometry
