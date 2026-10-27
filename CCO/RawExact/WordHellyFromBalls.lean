import CCO.RawExact.MeetHelly
import CCO.RawExact.ConvolutionFromHelly

/-!
# B002 C07: obtain full RAW word Helly from heterogeneous exact-ball Helly

This proof is source-faithful but reorders the claims: for each finite
family of word profiles with common endpoint sorts, choose ONE actual
right endpoint. Original named-sort transitivity and invariant RAW
words move every pairwise walk-profile witness to that endpoint.
Their singleton exact balls consequently meet pairwise, and C13
supplies one common left endpoint.

The C13 provider is explicitly visible and still requires the
private-word anchored fan proof. No instance of the conjectured
Helly property or any quotient homogeneity is postulated.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A noncircular alternative source derivation of C07 using C13.
Its only new mathematical input is the explicit full C13 provider;
the actual word invariance and original-sort transitivity follow
from the accepted original homogeneous source. -/
theorem wordProfileHelly_of_exactBallHelly
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S) :
    WordProfileHelly S := by
  intro i j P hNonempty hPair
  obtain ⟨b⟩ := S.nonemptySort j
  let D : Fin P.length → NonemptyExact S i j :=
    fun t => singletonExact S (P.get t)
      (hNonempty (P.get t) (List.get_mem P t))
  have hPairBalls : ∀ p q : Fin P.length,
      (ball (evaluate S (D p).words) b ∩
        ball (evaluate S (D q).words) b).Nonempty := by
    intro p q
    obtain ⟨x, z, hp, hq⟩ :=
      hPair (P.get p) (List.get_mem P p)
        (P.get q) (List.get_mem P q)
    obtain ⟨g, hg⟩ :=
      S.original_sort_transitive_of_homogeneous H j z b
    refine ⟨g • x, ?_, ?_⟩
    · change evaluate S [P.get p] (g • x) b
      rw [evaluate_single S]
      have hTrans := word_invariant_of_homogeneous S H
        (P.get p) g x z hp
      simpa only [hg] using hTrans
    · change evaluate S [P.get q] (g • x) b
      rw [evaluate_single S]
      have hTrans := word_invariant_of_homogeneous S H
        (P.get q) g x z hq
      simpa only [hg] using hTrans
  obtain ⟨x, hx⟩ :=
    hHelly (fun _ : Fin P.length => j) D
      (fun _ => b) hPairBalls
  refine ⟨x, b, ?_⟩
  intro word hw
  obtain ⟨t, ht⟩ := List.get_of_mem hw
  have hSingle := hx t
  change evaluate S [P.get t] x b at hSingle
  rw [evaluate_single S] at hSingle
  rw [← ht]
  exact hSingle

end CCO.RawExact
