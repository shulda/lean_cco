import CCO.TransitionClosure.OriginalTransportTargetFull
import CCO.QuotientTransport.Irreducible

/-!
# B049 source07 C35-C37: FULL original meet-irreducibility pullback

The accepted B040 upper-interval isomorphism acts on ALL invariant
equivalences under the actual original homogeneous group. The proved
old full-ColourEq / invariant-InvEq order isomorphism transports
the upper-interval source pullback back to one TRUE original FULL
colour-invariant equivalence H0, with J<=H0.

This module transfers proper meet-irreducibility, not merely
meet-irreducibility in an artificially restricted represented or
exact sublattice. No terminal NR2 or quotient SAP/CCO is used.
The selected further unique FULL cover, terminal represented
membership and named hidden-coordinate consumer remain separate.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open CCO.ParityHasse.Original
open CCO.QuotientTransport

/-- The exact source-side FULL original ColourEq pulled back from
a genuine target FULL L above F = Rᵒᵖ;J;R by the B040 interval
isomorphism. No independent quotient chart or represented-equivalence
hypothesis is introduced. -/
noncomputable def originalFullTransportPullColourEq
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (L : ColourEq S j)
    (hFL : originalTransportTargetColourEq S H J T ≤ L) :
    ColourEq S i :=
  (originalFullColourEqInvEqOrderIso S H).symm
    (T.pull (originalColourEqAsInvEq S H L)
      (fun y z hyz => hFL hyz))

/-- The pulled source FULL equivalence really lies above the
actual ORIGINAL J, as an inequality in the WHOLE old ColourEq
lattice, not in a restricted lattice of represented objects. -/
theorem originalFullTransportPullColourEq_source_le
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (L : ColourEq S j)
    (hFL : originalTransportTargetColourEq S H J T ≤ L) :
    J ≤ originalFullTransportPullColourEq S H J T L hFL := by
  intro x z hxz
  change (T.pull (originalColourEqAsInvEq S H L)
    (fun y z hyz => hFL hyz)) x z
  exact T.source_le_pull
    (originalColourEqAsInvEq S H L)
    (fun y z hyz => hFL hyz) hxz

/-- SOURCE C36 original FULL proper MI transport.
The original target L is a proper meet-irreducible in the
WHOLE ORIGINAL invariant-equivalence lattice iff its exact
FULL original source-side pullback H0 is also proper MI
in the WHOLE original invariant-equivalence lattice.

This consumes the actual B040 generic push_meetIrreducible and
push_pull equivalence, together with the already proved
SAME original ambient-G full lattice identification; it
assumes neither restricted-exact MI nor quotient SAP/CCO. -/
theorem originalFullTransportPullColourEq_properMI_iff
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (L : ColourEq S j)
    (hFL : originalTransportTargetColourEq S H J T ≤ L) :
    ProperMeetIrreducible (originalColourEqAsInvEq S H L) ↔
      ProperMeetIrreducible
        (originalColourEqAsInvEq S H
          (originalFullTransportPullColourEq S H J T L hFL)) := by
  let LV : InvEq G (X j) := originalColourEqAsInvEq S H L
  have hTL : T.target ≤ LV := by
    intro y z hyz
    exact hFL hyz
  let H0 : ColourEq S i :=
    originalFullTransportPullColourEq S H J T L hFL
  have hIso : originalColourEqAsInvEq S H H0 = T.pull LV hTL :=
    (originalFullColourEqInvEqOrderIso S H).apply_symm_apply (T.pull LV hTL)
  have hMI :=
    T.push_meetIrreducible (T.pull LV hTL) (T.source_le_pull LV hTL)
  rw [T.push_pull LV hTL] at hMI
  change ProperMeetIrreducible LV ↔
    ProperMeetIrreducible (originalColourEqAsInvEq S H H0)
  rw [hIso]
  exact hMI


/-- QuotientTransport.Transport.Covers of two equivalences above a fixed original kernel are
exactly their covers in the whole order, since all intermediate
equivalences also lie above that kernel. -/
private theorem covers_upper_interval_iff
    {α : Type*} [PartialOrder α] (E L K : α)
    (hEL : E ≤ L) (hEK : E ≤ K) :
    QuotientTransport.Transport.Covers (⟨L, hEL⟩ : {F : α // E ≤ F})
      (⟨K, hEK⟩ : {F : α // E ≤ F}) ↔ QuotientTransport.Transport.Covers L K := by
  constructor
  · rintro ⟨hlt, hgap⟩
    refine ⟨hlt, ?_⟩
    intro F hLF hFK
    rcases hgap ⟨F, hEL.trans hLF⟩ hLF hFK with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro ⟨hlt, hgap⟩
    refine ⟨hlt, ?_⟩
    intro F hLF hFK
    rcases hgap F.val hLF hFK with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

/-- An order isomorphism identifies covers in the complete
underlying orders; no distributivity or quotient SAP is used. -/
private theorem covers_orderIso_iff
    {α β : Type*} [PartialOrder α] [PartialOrder β]
    (e : α ≃o β) (L K : α) :
    QuotientTransport.Transport.Covers (e L) (e K) ↔ QuotientTransport.Transport.Covers L K := by
  constructor
  · rintro ⟨hlt, hgap⟩
    refine ⟨(e.lt_iff_lt).mp hlt, ?_⟩
    intro F hLF hFK
    rcases hgap (e F) (e.monotone hLF) (e.monotone hFK) with h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (e.injective h)
  · rintro ⟨hlt, hgap⟩
    refine ⟨(e.lt_iff_lt).mpr hlt, ?_⟩
    intro F hLF hFK
    rcases hgap (e.symm F)
        (by simpa using e.symm.monotone hLF)
        (by simpa using e.symm.monotone hFK) with h | h
    · exact Or.inl (by simpa using congrArg e h)
    · exact Or.inr (by simpa using congrArg e h)

/-- B040's actual interval isomorphism preserves the WHOLE
invariant-equivalence cover relation on its two full upper cones. -/
private theorem original_transport_pull_full_covers_iff
    {i j : ι} (E : InvEq G (X i))
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport E R)
    (L K : InvEq G (X j))
    (hFL : T.target ≤ L) (hFK : T.target ≤ K) :
    QuotientTransport.Transport.Covers L K ↔ QuotientTransport.Transport.Covers (T.pull L hFL) (T.pull K hFK) := by
  have hL : T.intervalIso
      ⟨T.pull L hFL, T.source_le_pull L hFL⟩ =
      (⟨L, hFL⟩ : {P : InvEq G (X j) // T.target ≤ P}) := by
    apply Subtype.ext
    exact T.push_pull L hFL
  have hK : T.intervalIso
      ⟨T.pull K hFK, T.source_le_pull K hFK⟩ =
      (⟨K, hFK⟩ : {P : InvEq G (X j) // T.target ≤ P}) := by
    apply Subtype.ext
    exact T.push_pull K hFK
  have hCov := T.intervalIso_covers
    (⟨T.pull L hFL, T.source_le_pull L hFL⟩ :
      {P : InvEq G (X i) // E ≤ P})
    (⟨T.pull K hFK, T.source_le_pull K hFK⟩ :
      {P : InvEq G (X i) // E ≤ P})
  rw [hL, hK] at hCov
  exact (covers_upper_interval_iff T.target L K hFL hFK).symm.trans
    (hCov.trans
      (covers_upper_interval_iff E (T.pull L hFL) (T.pull K hFK)
        (T.source_le_pull L hFL) (T.source_le_pull K hFK)))

/-- SOURCE07 C36: genuine FULL original unique-cover geometry is
preserved by actual B040 quotient transport. For target FULL old
equivalences L,K above the literal target kernel F, being a
cover in the whole original colour-invariant lattice is equivalent
to the pulled source FULL equivalences forming a cover.

The order intervals are the full original lattices, not the
represented/exact or quotient-age lattices. In particular this
conclusion does NOT require quotient SAP, CCO or NR2. -/
theorem originalFullTransportPullColourEq_covers_iff
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (L K : ColourEq S j)
    (hFL : originalTransportTargetColourEq S H J T ≤ L)
    (hFK : originalTransportTargetColourEq S H J T ≤ K) :
    QuotientTransport.Transport.Covers L K ↔
      QuotientTransport.Transport.Covers (originalFullTransportPullColourEq S H J T L hFL)
        (originalFullTransportPullColourEq S H J T K hFK) := by
  let LV : InvEq G (X j) := originalColourEqAsInvEq S H L
  let KV : InvEq G (X j) := originalColourEqAsInvEq S H K
  have hTL : T.target ≤ LV := by
    intro y z hyz
    exact hFL hyz
  have hTK : T.target ≤ KV := by
    intro y z hyz
    exact hFK hyz
  have hIsoL :
      originalColourEqAsInvEq S H
        (originalFullTransportPullColourEq S H J T L hFL) =
          T.pull LV hTL :=
    (originalFullColourEqInvEqOrderIso S H).apply_symm_apply (T.pull LV hTL)
  have hIsoK :
      originalColourEqAsInvEq S H
        (originalFullTransportPullColourEq S H J T K hFK) =
          T.pull KV hTK :=
    (originalFullColourEqInvEqOrderIso S H).apply_symm_apply (T.pull KV hTK)
  calc
    QuotientTransport.Transport.Covers L K ↔ QuotientTransport.Transport.Covers LV KV :=
      (covers_orderIso_iff (originalFullColourEqInvEqOrderIso S H) L K).symm
    _ ↔ QuotientTransport.Transport.Covers (T.pull LV hTL) (T.pull KV hTK) :=
      original_transport_pull_full_covers_iff
        (originalColourEqAsInvEq S H J) T LV KV hTL hTK
    _ ↔ QuotientTransport.Transport.Covers (originalFullTransportPullColourEq S H J T L hFL)
          (originalFullTransportPullColourEq S H J T K hFK) := by
        rw [← hIsoL, ← hIsoK]
        exact covers_orderIso_iff (originalFullColourEqInvEqOrderIso S H)
          (originalFullTransportPullColourEq S H J T L hFL)
          (originalFullTransportPullColourEq S H J T K hFK)


/-- A proper FULL invariant meet-irreducible has at most one cover.
The proof uses the full meet and the cover gap, not any modularity,
distributivity, exactness or quotient finiteness hypothesis. -/
private theorem original_full_properMI_cover_unique
    (H : HomogeneousSource S G)
    {i : ι} (J K L : ColourEq S i)
    (hMI : ProperMeetIrreducible (originalColourEqAsInvEq S H J))
    (hJK : QuotientTransport.Transport.Covers J K)
    (hJL : QuotientTransport.Transport.Covers J L) :
    K = L := by
  let e := originalFullColourEqInvEqOrderIso S H (i := i)
  have hVK : QuotientTransport.Transport.Covers
      (originalColourEqAsInvEq S H J) (originalColourEqAsInvEq S H K) :=
    (covers_orderIso_iff e J K).mpr hJK
  have hVL : QuotientTransport.Transport.Covers
      (originalColourEqAsInvEq S H J) (originalColourEqAsInvEq S H L) :=
    (covers_orderIso_iff e J L).mpr hJL
  let JV : InvEq G (X i) := originalColourEqAsInvEq S H J
  let KV : InvEq G (X i) := originalColourEqAsInvEq S H K
  let LV : InvEq G (X i) := originalColourEqAsInvEq S H L
  have hMeet : JV ≤ KV ⊓ LV := le_inf hVK.1.le hVL.1.le
  rcases hVK.2 (KV ⊓ LV) hMeet inf_le_left with hJ | hK
  · rcases hMI.2 KV LV hJ.symm with h | h
    · exact False.elim ((ne_of_lt hVK.1) h)
    · exact False.elim ((ne_of_lt hVL.1) h)
  · have hKL : KV ≤ LV := by
      calc
        KV = KV ⊓ LV := hK.symm
        _ ≤ LV := inf_le_right
    rcases hVL.2 KV hVK.1.le hKL with h | h
    · exact False.elim ((ne_of_gt hVK.1) h)
    · exact e.injective h

/-- SOURCE07 C36, including the UNIQUE FULL cover:
if a target FULL original equivalence L is proper MI and K
covers L, their precise full B040 pullbacks form a cover,
which is the ONLY cover above the pulled-back L anywhere
in the entire original source FULL equivalence lattice.

This is a statement about the two original homogeneous
sorts and genuine full orbit-invariant lattices. The
terminal FULL NR2 represented-name gate is independent. -/
theorem originalFullTransportPullColourEq_unique_full_cover
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (L K : ColourEq S j)
    (hFL : originalTransportTargetColourEq S H J T ≤ L)
    (hFK : originalTransportTargetColourEq S H J T ≤ K)
    (hLMI : ProperMeetIrreducible (originalColourEqAsInvEq S H L))
    (hLK : QuotientTransport.Transport.Covers L K) :
    QuotientTransport.Transport.Covers
        (originalFullTransportPullColourEq S H J T L hFL)
        (originalFullTransportPullColourEq S H J T K hFK) ∧
      ∀ V : ColourEq S i,
        QuotientTransport.Transport.Covers
            (originalFullTransportPullColourEq S H J T L hFL) V →
          V = originalFullTransportPullColourEq S H J T K hFK := by
  have hCover :=
    (originalFullTransportPullColourEq_covers_iff
      S H J T L K hFL hFK).mp hLK
  have hMI :=
    (originalFullTransportPullColourEq_properMI_iff
      S H J T L hFL).mp hLMI
  refine ⟨hCover, ?_⟩
  intro V hV
  exact original_full_properMI_cover_unique S H
    (originalFullTransportPullColourEq S H J T L hFL)
    V (originalFullTransportPullColourEq S H J T K hFK)
    hMI hV hCover


/-- SOURCE07 C36-C37: a proper FULL meet-irreducible on the
original source sort transports to a proper FULL meet-irreducible
on the original target sort. This is the B040 interval
isomorphism on the WHOLE original-G invariant lattice:
the target is the LITERAL Rᵒᵖ;J;R kernel, not an independently
chosen represented quotient chart. No SAP, CCO or NR2 here. -/
theorem originalTransportTargetColourEq_full_properMI
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    (hJMI : ProperMeetIrreducible (originalColourEqAsInvEq S H J))
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R) :
    ProperMeetIrreducible
      (originalColourEqAsInvEq S H
        (originalTransportTargetColourEq S H J T)) := by
  let E : InvEq G (X i) := originalColourEqAsInvEq S H J
  have hPush : T.push E le_rfl = T.target := by
    apply InvEq.ext
    intro y z
    exact (T.push_iff E le_rfl y z).trans (T.target_iff y z).symm
  have hTarget : ProperMeetIrreducible T.target := by
    rw [← hPush]
    exact (T.push_meetIrreducible E le_rfl).mpr hJMI
  have hNamed : originalColourEqAsInvEq S H
      (originalTransportTargetColourEq S H J T) = T.target :=
    (originalFullColourEqInvEqOrderIso S H).apply_symm_apply T.target
  rw [hNamed]
  exact hTarget

/-- SOURCE07 C37, kept distinct from generic interval transport:
under the original old SAP and explicit original terminal FULL NR2,
the true transported kernel is a NONIDENTITY, proper FULL
meet-irreducible and possesses a SINGLE ACTUAL equality-inclusive
original RAW atomic word. This justifies represented membership;
no assertion of a positive STRONG presentation, quotient SAP/CCO
or choice of a fake target equivalence is made.

The source is explicitly nonidentity J and proper FULL MI.
The upper bound J<Top is DERIVED here from the proper FULL
meet-irreducibility hypothesis; it is NOT an extra premise.
The old SAP noncollapse API then consumes this consequence. -/
theorem originalTransportTargetColourEq_properMI_named_NR2
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (J : ColourEq S i)
    (hJbot : (⊥ : ColourEq S i) < J)
    (hJMI : ProperMeetIrreducible (originalColourEqAsInvEq S H J))
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R) :
    ProperMeetIrreducible
        (originalColourEqAsInvEq S H
          (originalTransportTargetColourEq S H J T)) ∧
      (⊥ : ColourEq S j) < originalTransportTargetColourEq S H J T ∧
      originalTransportTargetColourEq S H J T < (⊤ : ColourEq S j) ∧
      ∃ word : RawWord S j j,
        RawWord.relation S word =
          (originalTransportTargetColourEq S H J T).val.r := by
  have hJnotTop : J ≠ (⊤ : ColourEq S i) := by
    intro hJE
    apply hJMI.1
    apply InvEq.ext
    intro x y
    constructor
    · intro _
      exact (InvEq.top_apply x y).mpr trivial
    · intro _
      have hxy : J x y := by
        rw [hJE]
        exact (ColourEq.top_apply S i x y).mpr trivial
      exact hxy
  have hJtop : J < (⊤ : ColourEq S i) :=
    lt_of_le_of_ne le_top hJnotTop
  obtain ⟨hBot,hTop⟩ :=
    originalTransportTargetColourEq_proper_nonzero
      S H sap J hJbot hJtop T
  exact ⟨originalTransportTargetColourEq_full_properMI
      S H J hJMI T, hBot, hTop,
    originalTransportTargetColourEq_raw_word_of_NR2 S H nr2 J T⟩

end CCO.TransitionClosure
