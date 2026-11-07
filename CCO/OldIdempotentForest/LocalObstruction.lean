import CCO.GuardedOldSeams.LiftFinite

/-! A failed bounded complete OLD pair pattern is itself a bounded
noncompletable induced closed source. This uses actual irreducibility;
a reducible pair of ancestors is never substituted for that support. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.UnarySupport CCO.UnarySupport.Structure

section General
variable {L : Signature.{u}} {P : Type v} {Q : Type w}
variable (C : Structure L P)

theorem irreducible_induce_univ (hU : C.IsClosed Set.univ)
    (hC : C.Irreducible) : (C.induce Set.univ hU).Irreducible := by
  constructor
  intro d
  apply hC.false
  refine {
    left := Subtype.val '' d.left
    right := Subtype.val '' d.right
    left_closed := C.isClosed_image hU d.left_closed
    right_closed := C.isClosed_image hU d.right_closed
    cover := ?_
    left_proper := ?_
    right_proper := ?_
    rel_local := ?_ }
  · apply Set.eq_univ_of_forall
    intro x
    have hx : (⟨x,Set.mem_univ x⟩ : (Set.univ : Set P)) ∈ d.left ∪ d.right := by
      rw [d.cover]
      trivial
    rcases hx with hx | hx
    · exact Or.inl ⟨⟨x,Set.mem_univ x⟩,hx,rfl⟩
    · exact Or.inr ⟨⟨x,Set.mem_univ x⟩,hx,rfl⟩
  · intro he
    apply d.left_proper
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.val ∈ Subtype.val '' d.left := by rw [he]; trivial
    obtain ⟨y,hy,hyx⟩ := hx
    exact (Subtype.ext hyx) ▸ hy
  · intro he
    apply d.right_proper
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.val ∈ Subtype.val '' d.right := by rw [he]; trivial
    obtain ⟨y,hy,hyx⟩ := hx
    exact (Subtype.ext hyx) ▸ hy
  · intro R xs h
    let ys : Fin (L.arity R) → (Set.univ : Set P) := fun i => ⟨xs i,Set.mem_univ _⟩
    rcases d.rel_local R ys h with hl | hr
    · exact Or.inl (fun i => ⟨ys i,hl i,rfl⟩)
    · exact Or.inr (fun i => ⟨ys i,hr i,rfl⟩)

/-- On an irreducible entire source, the actual HE condition gives an
induced embedding with complete unary domain reflection. -/
def embeddingOfHomEmbeddingIrreducible {A : Structure L Q}
    (f : Hom C A) (hf : f.HomEmbedding) (hC : C.Irreducible) : Embedding C A := by
  let hU : C.IsClosed Set.univ := by intro F x hx y hy; trivial
  have hu := hf Set.univ hU (irreducible_induce_univ C hU hC)
  exact {
    point := f.point
    sort_eq := f.sort_eq
    map_func := f.map_func
    map_rel := f.map_rel
    injective := by
      intro x y h
      exact hu.1 (Set.mem_univ x) (Set.mem_univ y) h
    reflect_func := by
      intro F x y hy
      obtain ⟨z,_,hz,he⟩ := hu.2.2 F x (Set.mem_univ x) y hy
      exact ⟨z,hz,he⟩
    reflect_rel := fun R xs h => (hu.2.1 R xs (fun _ => Set.mem_univ _)).mp h }

end General

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.GuardedTwoRoot CCO.GuardedOldSeams
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

theorem irreducible_no_finite_hidden_completion
    (hF : F.Irreducible)
    (hNo : ¬ Nonempty (Embedding F (originalPartialTarget S H sap nr2))) :
    ¬ FiniteHiddenCompletion S H sap nr2 F := by
  rintro ⟨D,_,hD,f,hf⟩
  exact hNo ⟨embeddingOfHomEmbeddingIrreducible F
    (closedInducedHom hD f) (closedInducedHom_HE hD f hf) hF⟩

/-- The failed test selects precisely an actual irreducible OLD joined
support. No global completion of the surrounding source is a premise. -/
theorem failed_bounded_pair_has_small_obstruction
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (hTests : ¬ BoundedJoinedPairTests S H sap nr2 F) :
    ∃ (D : Set P) (hD : F.IsClosed D),
      Nat.card D ≤ 2 * originalSourceUniformNormalCodeBudget S H ∧
      ¬ FiniteHiddenCompletion S H sap nr2 (F.induce D hD) := by
  classical
  have hw : ∃ b c : P, b ≠ c ∧ (F.closureStructure {b,c}).Irreducible ∧
      ¬ Nonempty (Embedding (F.closureStructure {b,c}) (originalPartialTarget S H sap nr2)) := by
    by_contra hn
    apply hTests
    intro b c hbc hirr _
    by_contra he
    exact hn ⟨b,c,hbc,hirr,he⟩
  obtain ⟨b,c,_,hirr,hNo⟩ := hw
  exact ⟨F.closure {b,c},F.isClosed_closure {b,c},
    actual_pair_support_bound S H sap nr2 F hUnary b c,
    irreducible_no_finite_hidden_completion S H sap nr2 (F.closureStructure {b,c}) hirr hNo⟩

/-- The actual singleton witnesses bound the closure of any chosen OLD
generators. The theorem fills no relation and asserts no completion. -/
theorem old_source_generated_card
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (B : Finset P) (K : ℕ) (hB : B.card ≤ K) :
    Nat.card (F.closure (B : Set P)) ≤ originalSourceUniformNormalCodeBudget S H * K := by
  have hm := singleton_bound_of_unary_admissible hUnary (actual_partial_singleton_budget S H sap nr2)
  simpa only [Nat.mul_comm] using
    SourceSupport.generated_support_card F B hB (fun b _ => hm b)

end CCO.OldIdempotentForest
