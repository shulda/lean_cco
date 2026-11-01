import CCO.TerminalLattice.OriginalStrongMenuChain
import CCO.TerminalLattice.PositiveOccurrenceLength
import CCO.StrongExact.ProfileSemantics

/-!
# B050 C26/C27: genuine MANY positive old typed private paths on each pair

The independent source08 theta-cycle guard permits several distinct
positive original typed branches for each root/centre or graph pair.
Its assigned nonempty STRONG menu needs only to be CONTAINED in every
branch's true old endpoint profile. No exact-profile equality, chosen
one-word-per-edge presentation, quotient-level CCO or strong identity
is part of this construction.

We instantiate the accepted B002 private-path engine with an actual
list of whole positive OLD typed words on each canonical unordered
marked pair. For every present pair, one fine atom from its assigned
menu is realized by ONE real old source pair and EVERY branch word;
old source homogeneity transports each original positive word's
representability to that fixed pair. For absent pairs, the presentation
is literally empty. All used words have positive original length,
including arbitrary intermediate named sorts.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- If the fine original colour of a REAL pair belongs to the STRONG
profile of an old positive typed word, the word's actual RAW
represented relation holds at precisely THOSE endpoints.

This is proved from original homogeneous pair transport of the
positive word realization, not an extra positive-state realization
provider or a quotient reduct action. -/
theorem originalPositiveWord_represented_of_menuRel
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (D : S.Menu i i)
    (p : PositiveWord S i i)
    (hD : D ⊆ PositiveWord.profile S p)
    (x y : X i) (hXY : S.menuRel D x y) :
    PositiveWord.represented S p x y := by
  obtain ⟨a,ha,hColXY⟩ := hXY
  obtain ⟨u,v,hRep,hColUV⟩ :=
    (StrongExact.positive_profile_iff_represented
      S H sap p a).mp (hD ha)
  obtain ⟨g,hgu,hgv⟩ :=
    S.pair_homogeneous_of_homogeneous H
      u x v y (hColUV.trans hColXY.symm)
  have hMove :=
    (PositiveWord.represented_invariant_of_homogeneous S H p)
      g u v hRep
  simpa only [hgu,hgv] using hMove

/-- An ACTUAL finite family of original positive atomic typed words
for each canonical pair. Multiple words create pairwise disjoint
private interiors, precisely as in ACCEPTED B002's literal expansion.
An empty family creates no path, never a synthetic equality edge. -/
def originalThetaPresentations {i : ι} {n : Nat}
    (families : CCO.RawExact.QuotientExpansion.Edge n →
      List (PositiveWord S i i)) :
    CCO.RawExact.QuotientExpansion.Menus S (fun _ : Fin n => i) :=
  fun e => (families e).map (PositiveWord.toRawWord S)

/-- All private presentations have actual OLD real endpoint pairs.
For a nonempty theta gadget the selected source menu D_e is a
genuine NONEMPTY fine STRONG menu and belongs to EVERY branch's
positive endpoint profile. Thus ONE pair of a fixed fine atom in D_e
realizes ALL its words simultaneously. Empty families impose Top. -/
theorem originalThetaPresentations_nonempty
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (families : CCO.RawExact.QuotientExpansion.Edge n →
      List (PositiveWord S i i))
    (guards : CCO.RawExact.QuotientExpansion.Edge n → S.Menu i i)
    (hGuard : ∀ e, families e ≠ [] →
      (guards e).Nonempty ∧
      ∀ p ∈ families e, guards e ⊆ PositiveWord.profile S p) :
    ∀ e, TRel.Nonempty
      (CCO.RawExact.evaluate S
        (originalThetaPresentations S families e)) := by
  intro e
  by_cases hEmpty : families e = []
  · obtain ⟨x⟩ := S.nonemptySort i
    refine ⟨x,x,?_⟩
    intro raw hRaw
    have hNo : raw ∈ ([] : List (CCO.RawWord S i i)) := by
      simpa [originalThetaPresentations,hEmpty] using hRaw
    simp at hNo
  · obtain ⟨⟨a,ha⟩,hSubs⟩ := hGuard e hEmpty
    obtain ⟨x,y,hCol⟩ := S.realized a
    refine ⟨x,y,?_⟩
    intro raw hRaw
    have hMem :
        raw ∈ (families e).map (PositiveWord.toRawWord S) := by
      simpa only [originalThetaPresentations] using hRaw
    obtain ⟨p,hp,hEq⟩ := List.mem_map.mp hMem
    subst raw
    rw [← PositiveWord.represented_toRawWord S p]
    exact originalPositiveWord_represented_of_menuRel
      S H sap (guards e) p (hSubs p hp)
        x y ⟨a,ha,hCol⟩

/-- Every ACTUAL private occurrence in a genuine multiple-word
theta presentation has positive OLD diversity length. There is no
zero-length STRONG unit, and omitted families have zero occurrences.
-/
theorem originalThetaPresentations_occurrence_positive
    {i : ι} {n : Nat}
    (families : CCO.RawExact.QuotientExpansion.Edge n →
      List (PositiveWord S i i))
    (o : CCO.RawExact.QuotientExpansion.Occurrence S
      (fun _ : Fin n => i) (originalThetaPresentations S families)) :
    0 < CCO.RawExact.diversityLength S
      (CCO.RawExact.QuotientExpansion.word S
        (fun _ : Fin n => i) (originalThetaPresentations S families) o) := by
  let P := originalThetaPresentations S families
  rcases o with ⟨e,slot⟩
  have hMem :
      CCO.RawExact.QuotientExpansion.word S (fun _ : Fin n => i)
        P ⟨e,slot⟩ ∈ P e :=
    List.get_mem (P e) slot
  have hMem' :
      CCO.RawExact.QuotientExpansion.word S (fun _ : Fin n => i)
        P ⟨e,slot⟩ ∈
          (families e).map (PositiveWord.toRawWord S) := by
    simpa only [P,originalThetaPresentations] using hMem
  obtain ⟨p,hp,hEq⟩ := List.mem_map.mp hMem'
  rw [← hEq]
  exact oldPositiveWord_diversityLength_pos S p

/-- The single honest ORIGINAL partial atomic diagram containing
every positive old private theta branch, with the accepted B002
path-specific intermediate named sorts and pairwise private
interiors. Neither original CCO nor SAP on the quotient is invoked
to create this syntax. -/
noncomputable def originalThetaDiagram
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (families : CCO.RawExact.QuotientExpansion.Edge n →
      List (PositiveWord S i i))
    (guards : CCO.RawExact.QuotientExpansion.Edge n → S.Menu i i)
    (hGuard : ∀ e, families e ≠ [] →
      (guards e).Nonempty ∧
      ∀ p ∈ families e, guards e ⊆ PositiveWord.profile S p) :
    PartialDiagram S
      (CCO.RawExact.QuotientExpansion.Vertex S
        (fun _ : Fin n => i) (originalThetaPresentations S families)) :=
  CCO.RawExact.QuotientExpansion.diagram S
    (fun _ : Fin n => i) (originalThetaPresentations S families)
      (originalThetaPresentations_nonempty S H sap families guards hGuard)

end CCO.TerminalLattice
