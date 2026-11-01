import CCO.TerminalLattice.OriginalModularity
import CCO.RawExact.ExactBallHellySource
import CCO.RealClosure.Bounds.TerminalWords
import Mathlib.Tactic.FinCases

/-!
# B050 C07–C09: an actual RAW-word M₃ contradicts ORIGINAL semantic CCO

This consumes the ACCEPTED B002 theorem `exact_ball_helly_of_CCO`,
whose proof constructs/validates a finite private-path original diagram
and uses original CCO, without SAP. We explicitly create the three
one-word ORIGINAL exact balls at the two distinct centres, prove each
pair intersects, and derive the empty-triple contradiction.

There is NO assumption that arbitrary abstract finite lattice elements
have words; C09 obtains the three actual words ONLY from accepted B011
under FULL original NR2, without using its CCO-distributivity conclusion.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- One equality-inclusive original RAW word representing an original
invariant equivalence is a nonempty exact presentation because it
contains the genuine diagonal. This needs no CCO or SAP. -/
private def originalEquivWordExact {i : ι}
    (E : ColourEq S i) (word : RawWord S i i)
    (hw : RawWord.relation S word = E.val.r) :
    RawExact.NonemptyExact S i i := by
  refine ⟨[word], ?_⟩
  obtain ⟨a⟩ := S.nonemptySort i
  refine ⟨a, a, ?_⟩
  change ∀ w, w ∈ [word] → RawWord.relation S w a a
  intro w hm
  have heq : w = word := by simpa only [List.mem_singleton] using hm
  subst w
  exact Eq.mp (congrFun (congrFun hw a) a).symm (E.val.refl a)

private theorem originalEquivWordExact_evaluate {i : ι}
    (E : ColourEq S i) (word : RawWord S i i)
    (hw : RawWord.relation S word = E.val.r) :
    RawExact.evaluate S (originalEquivWordExact S E word hw).words = E.val.r := by
  change RawExact.evaluate S [word] = E.val.r
  rw [RawExact.evaluate_single S, hw]

/-- C07–C08: the actual three J-class constraints in an M₃ would
have a common original real solution if the whole source had semantic
CCO. Contradiction: the three pairwise classes have empty total meet.

The finite private-path argument is not postulated. It is precisely the
already accepted source-strength B002 `exact_ball_helly_of_CCO`
construction for our THREE one-word singleton presentations, with
centres x, x and y and arbitrary original intermediate named sorts. -/
theorem original_m3_words_forbid_CCO
    (H : HomogeneousSource S G) {i : ι}
    (E₁ E₂ E₃ L K : ColourEq S i)
    (hMeet12 : E₁ ⊓ E₂ = L)
    (hMeet13 : E₁ ⊓ E₃ = L)
    (hJoin12 : ColourEq.join S H E₁ E₂ = K)
    (hJoin23 : ColourEq.join S H E₂ E₃ = K)
    (hProper : L < E₁)
    (w₁ w₂ w₃ : RawWord S i i)
    (hw₁ : RawWord.relation S w₁ = E₁.val.r)
    (hw₂ : RawWord.relation S w₂ = E₂.val.r)
    (hw₃ : RawWord.relation S w₃ = E₃.val.r) :
    ¬ SemanticCCO.{u,v,max u v,w} S := by
  classical
  intro cco
  obtain ⟨x, y, z, hxy, hnotL, hxz, hzy, hNoTriple⟩ :=
    actual_m3_classes S H E₁ E₂ E₃ L K
      hMeet12 hMeet13 hJoin12 hJoin23 hProper
  let d₁ := originalEquivWordExact S E₁ w₁ hw₁
  let d₂ := originalEquivWordExact S E₂ w₂ hw₂
  let d₃ := originalEquivWordExact S E₃ w₃ hw₃
  have hd₁ : RawExact.evaluate S d₁.words = E₁.val.r :=
    originalEquivWordExact_evaluate S E₁ w₁ hw₁
  have hd₂ : RawExact.evaluate S d₂.words = E₂.val.r :=
    originalEquivWordExact_evaluate S E₂ w₂ hw₂
  have hd₃ : RawExact.evaluate S d₃.words = E₃.val.r :=
    originalEquivWordExact_evaluate S E₃ w₃ hw₃
  let d : Fin 3 → RawExact.NonemptyExact S i i :=
    fun p => if p = 0 then d₁ else if p = 1 then d₂ else d₃
  let centre : Fin 3 → X i :=
    fun p => if p = 2 then y else x
  have h00 :
      (RawExact.ball E₁.val.r x ∩ RawExact.ball E₁.val.r x).Nonempty :=
    ⟨x, E₁.val.refl x, E₁.val.refl x⟩
  have h01 :
      (RawExact.ball E₁.val.r x ∩ RawExact.ball E₂.val.r x).Nonempty :=
    ⟨x, E₁.val.refl x, E₂.val.refl x⟩
  have h02 :
      (RawExact.ball E₁.val.r x ∩ RawExact.ball E₃.val.r y).Nonempty :=
    ⟨y, E₁.val.symm hxy, E₃.val.refl y⟩
  have h10 :
      (RawExact.ball E₂.val.r x ∩ RawExact.ball E₁.val.r x).Nonempty :=
    ⟨x, E₂.val.refl x, E₁.val.refl x⟩
  have h11 :
      (RawExact.ball E₂.val.r x ∩ RawExact.ball E₂.val.r x).Nonempty :=
    ⟨x, E₂.val.refl x, E₂.val.refl x⟩
  have h12 :
      (RawExact.ball E₂.val.r x ∩ RawExact.ball E₃.val.r y).Nonempty :=
    ⟨z, E₂.val.symm hxz, hzy⟩
  have h20 :
      (RawExact.ball E₃.val.r y ∩ RawExact.ball E₁.val.r x).Nonempty :=
    ⟨y, E₃.val.refl y, E₁.val.symm hxy⟩
  have h21 :
      (RawExact.ball E₃.val.r y ∩ RawExact.ball E₂.val.r x).Nonempty :=
    ⟨z, hzy, E₂.val.symm hxz⟩
  have h22 :
      (RawExact.ball E₃.val.r y ∩ RawExact.ball E₃.val.r y).Nonempty :=
    ⟨y, E₃.val.refl y, E₃.val.refl y⟩
  have hPair (p q : Fin 3) :
      (RawExact.ball (RawExact.evaluate S (d p).words) (centre p) ∩
        RawExact.ball (RawExact.evaluate S (d q).words) (centre q)).Nonempty := by
    fin_cases p <;> fin_cases q
    all_goals
      first
      | simpa [d, centre, hd₁, hd₂, hd₃] using h00
      | simpa [d, centre, hd₁, hd₂, hd₃] using h01
      | simpa [d, centre, hd₁, hd₂, hd₃] using h02
      | simpa [d, centre, hd₁, hd₂, hd₃] using h10
      | simpa [d, centre, hd₁, hd₂, hd₃] using h11
      | simpa [d, centre, hd₁, hd₂, hd₃] using h12
      | simpa [d, centre, hd₁, hd₂, hd₃] using h20
      | simpa [d, centre, hd₁, hd₂, hd₃] using h21
      | simpa [d, centre, hd₁, hd₂, hd₃] using h22
  obtain ⟨root, hr⟩ :=
    RawExact.exact_ball_helly_of_CCO S H cco
      (fun _ : ULift.{max u v} (Fin 3) => i)
      (fun p => d p.down)
      (fun p => centre p.down)
      (fun p q => hPair p.down q.down)
  have hroot₁ : E₁ root x := by
    simpa [d, centre, hd₁] using (hr ⟨(0 : Fin 3)⟩)
  have hroot₂ : E₂ root x := by
    simpa [d, centre, hd₂] using (hr ⟨(1 : Fin 3)⟩)
  have hroot₃ : E₃ root y := by
    simpa [d, centre, hd₃] using (hr ⟨(2 : Fin 3)⟩)
  exact hNoTriple ⟨root, E₁.val.symm hroot₁,
    E₂.val.symm hroot₂, E₃.val.symm hroot₃⟩

/-- C09 source wrapper: FULL original NR2 supplies ACTUAL one-word
presentations for every original invariant equivalence, WITHOUT CCO or SAP.
No invocation of the downstream B011 full distributivity theorem occurs. -/
theorem original_m3_forbid_CCO_of_NR2
    (H : HomogeneousSource S G) {i : ι}
    (nr2 : RealClosure.Bounds.SortNR2 S i)
    (E₁ E₂ E₃ L K : ColourEq S i)
    (hMeet12 : E₁ ⊓ E₂ = L)
    (hMeet13 : E₁ ⊓ E₃ = L)
    (hJoin12 : ColourEq.join S H E₁ E₂ = K)
    (hJoin23 : ColourEq.join S H E₂ E₃ = K)
    (hProper : L < E₁) :
    ¬ SemanticCCO.{u,v,max u v,w} S := by
  obtain ⟨w₁, hw₁⟩ := RealClosure.Bounds.terminal_one_raw_word S H nr2 E₁
  obtain ⟨w₂, hw₂⟩ := RealClosure.Bounds.terminal_one_raw_word S H nr2 E₂
  obtain ⟨w₃, hw₃⟩ := RealClosure.Bounds.terminal_one_raw_word S H nr2 E₃
  exact original_m3_words_forbid_CCO S H E₁ E₂ E₃ L K
    hMeet12 hMeet13 hJoin12 hJoin23 hProper
    w₁ w₂ w₃ hw₁ hw₂ hw₃

end CCO.TerminalLattice
