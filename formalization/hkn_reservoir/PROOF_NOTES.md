# B027 proof notes — finite locality and a completable HKN reservoir

Frozen mathematical source 490c3f36. All seven new local source results are expanded below relative to the explicitly PUBLISHED HKN providers E01/E02 and prepared B025/B026 source interfaces. No CCO encoding adapter has been compiled, no new HKN proof is requested, and no global source-relative EPPA certification follows. Source TeX remains unchanged. The external theorem source is arXiv:1902.03855v4; its unary set-function definitions, global-language maps and tree-piece property are part of the inspected interface.

## N01: Proper-profile acyclicity, exact prefix count and bounded cycles

### L01 Proper-profile graph

Fix starting sort s. Its vertices are (t,D) where empty != D proper subset P_st is a profile of a POSITIVE typed word. An edge appends one actual atom a in P_tu and retains the resulting state only when D*a is proper. Every positive prefix profile is nonempty by SAP. Full states are absorbing by B026 absorption.

There are at most N_s=sum_t(2^|P_st|-2) vertices, because each t permits at most that many nonempty proper subsets. Reachable-profile restriction only decreases the count.

### L02 Acyclicity

If a state (t,D) recurs after a nonempty word, let W subset P_tt be its positive closed-word profile. It is nonempty by SAP and D*W=D. Associativity gives D*W^r=D for every positive r. B026 arbitrary-subset primitive-loop saturation makes W^r=P_tt for sufficiently large r; absorption then makes D=P_st, contradiction.

This uses W as a genuine nonempty loop subset. No STRONG identity or empty word is added and no exact-menu premise is needed.

### L03 Word-length bound without an extra +1

A positive word of r >= 1 letters has exactly r positive-prefix positions, numbered 1,...,r. If its final profile is proper, every prefix is proper because fullness is absorbing. Those r prefix states form a directed path with no repetitions, so r <= N_s.

Therefore ell=max_s N_s works: every word of length >ell is full. Do not count an index-zero empty-word state; that state does not exist in the strong diversity automaton. If all palettes are singletons then ell=0 and every one-letter word is already full, which is correct.

The source's wording “ell <= max_s sum_t(...)” is thus realized by choosing the displayed bound itself; a sharper longest reachable proper-prefix length is optional.

### L04 Cycle/strong-profile criterion

For a specified SIMPLE typed cycle on m >=3 distinct formal vertices, remove the closing edge. Its path has exactly m-1 letters and its closing atom c belongs to the endpoint pair palette with the appropriate converse orientation. The cycle has an actual homomorphism iff c lies in that path's STRONG profile:
- a strong profile witness gives an injective cycle realization immediately;
- conversely a cycle homomorphism cannot merge the two endpoints of its closing diversity edge. SAP injectivization fixes that complete actual endpoint edge and makes all auxiliary vertices distinct, yielding a strong path witness.

Thus homomorphic cycle semantics and strong endpoint composition agree here by the actual SAP bridge, not by definition alone. Repeated SORT labels do not affect the distinct formal vertices.

### L05 Bad-cycle and whole-diagram bound

If m-1>ell, the path profile is full and contains c. Hence every bad simple cycle has m<=ell+1; b=max(3,ell+1) is a valid coarse bound, including ell=0. For an arbitrary finite partial origin diagram P, if every specified simple cycle of LENGTH at most b maps to U_B, all longer specified cycles map automatically; P itself has no size bound. Semantic typed HOMOMORPHIC CCO yields a homomorphic completion of the entire origin diagram; use B025 packet-separated injective completion separately where required.

The state bound uses SAP+primitivity/symmetry; only this final entire-diagram CCO step uses CCO. The bound is calculated after B is fixed and need not be uniform across quotient witnesses.

## N02: Published providers, actual representation and exact requested components

**E01 — Theorem 1.1.** In a relation/unary-set-function signature with an
arity-preserving language group, finite A with finite relabel orbit has a finite
coherent EPPA witness W, irreducible-structure faithful for A.

**E02 — Theorem 1.2.** Given finite irreducible A, finite EPPA witness W for A
and integer n≥1, obtain finite B0 with EPPA and irreducible faithfulness for A,
a homomorphism-embedding B0→W, and, for every closed C≤B0 with |C|≤n,
a homomorphism-embedding C→D into a finite tree of full Gamma_L-isomorphic
A-copies. Coherence of W transfers.

**E03 — definitions and tree support.** A map has one global language
permutation. Embeddings preserve whole function-value sets by equality;
homomorphisms only require inclusion. Homomorphism-embeddings embed every
irreducible substructure. Tree overlaps lie in source copies; an irreducible
tree-piece lies in a source copy (Observation 9.3).

These are PUBLISHED external mathematical providers, not locally proved module
claims or newly compiled Lean imports. Their composition is E01(A), then
E02(A,W,n). An initial faithful W is allowed; E02 actually needs only EPPA.

## 2. Actual CCO signature and discharged hypotheses

This section is the application proof for the specific local source, not an
additional assertion of the external theorem.

Fix the finite actual owner set B, finite original fine palette, finite thin
group G, Gamma≤Aut(B), and nonempty complete full-packet A⊆N_B from the source.

Use unary relations O_b (b∈B), binary original fine relations R_a, and unary
function symbols t_g (g∈G). Interpret each ordinary source function as the
singleton-valued set function {t_g(x)}. No constant or higher-arity function is
introduced. Gamma sends O_b to O_(gamma b) and fixes every R_a and t_g. It
therefore preserves arities and symbol kinds. The whole signature is finite,
and Gamma is finite because B is finite; the relabel orbit of A has at most
|Gamma| members. This discharges E01's finite-orbit condition explicitly.

A is finite by assumption and is irreducible: any proposed free splitting
placing two vertices in different off-overlap parts contradicts the fine
binary relation on that pair, since A is complete. A one-point/one-packet
degeneracy poses no problem. The unary functions make every nonempty closed
part of A a union of complete real G-packets. Thus A is a valid E02 input.
Choose n=max(1,b|G|), where b=max(3,ell+1) is obtained after fixing B. In fact
G contains its identity and b≥3, so n=b|G|≥1.

Every Gamma relabel of A is realized in the actual N_B age by the prepared
pure-owner ambient lift (B025 C24), fixing literal fine names and commuting
with all named t_g. Separate lifts suffice; no coherent section
Gamma→Aut(N_B) is required. This realization is needed later for tree
completion, not as an additional hypothesis of E01.

## 3. Partial requests, saturation and ALL empty-domain components

Represent a requested map by the PAIR (gamma,p), retaining gamma even if p has
empty real domain.

For nonempty original real p with domain/range in A, its G-saturation is
well-defined: if t_g x=t_h y in the domain saturation, the appropriate thin
q_(g+h) relation between x,y and preservation by p gives
t_g p(x)=t_h p(y). The same argument for p inverse proves injectivity of the
saturation. Thin colour transport preserves all colours between saturated
points. Owner compatibility and gamma commuting with G give the correct
owner labels, and the saturated map commutes with each t_g. Its domain and
range are unions of whole packets because A is full-packet closed. Thus the
saturation is a genuine partial Gamma_L-isomorphism of A.

There are only finitely many such pairs, since both A and Gamma are finite.
The empty set is functionally closed because this signature has no nullary
functions. Every (gamma,empty) is therefore a genuine partial automorphism,
with vacuous vertex/colour/function conditions. E01/E02 extend these requests
too. Consequently the later language-action readout is onto ALL Gamma, not
just components visible on nonempty real domains. This is also directly
corroborated by HKN's empty-request discussion in §5.

### Distinguished-copy normalization is essential for exact components

If the external provider is supplied along an arbitrary distinguished
embedding psi=(lambda,psi_V):A→B0, first globally relabel B0 by lambda^{-1}.
The new distinguished embedding has identity language component; then rename
the finite vertices so A is literally a substructure. EPPA, faithfulness and
local trees transport under this Gamma_L-isomorphism.

Without this normalization, an extension along psi has language component
lambda gamma lambda^{-1}, rather than gamma in general. Thus a future Lean
adapter must expose the exact embedding/extension square and prove the
normalization; it must not simply erase psi's language component.
The local source already works with literal A⊆B0, so this is an explicit
implementation/contract bridge, not a new mathematical gap.

## N03: Actual closed-SAP tree realizations

### T01 Every relabelled source copy is actual

For each allowed gamma separately, its actual owner lift embeds gamma A into N_B while fixing fine atom names and commuting with every named t_g. The compatibility with owner/translation equations is part of the actual pure-owner source interface. No simultaneous choice or group section is used.

### T02 Every attachment overlap is full-packet closed

A substructure in this unary-function language contains all t_g values of each of its points. In a regular total source copy A this means a union of entire G-packets. Each tree attachment overlap S is a substructure of a constituent complete A-copy, so its displayed fine structure is complete and its image satisfies F[S]=S.

### T03 Finite tree induction

Maintain a COMPLETE induced actual N_B-realization of all vertices already attached. Extra completed colours between old pieces may be forgotten when returning to the partial tree. For a new source A-copy, its intersection S with the old tree is a complete full-packet substructure. Existing and new induced structures on S agree on all actual fine colours, owners and t_g. Named-owner homogeneity aligns the new copy's S with the old image; closed SAP C26 amalgamates their complete realizations with no off-base identifications. Embed the resulting finite actual amalgam into N_B over the entire old complete realization using its homogeneous extension property.

The complete old realization is preserved, not merely the partial tree. Since the tree records impose no additional old/new cross edges outside the source copy, arbitrary new amalgam colours cause no conflict. Iterate finitely. If a whole source copy is prescribed, root the tree construction at that copy and keep it fixed throughout.

Conclusion: the entire free tree has an INJECTIVE record-preserving homomorphism into N_B; on each complete source copy it is an induced embedding. The map does not reflect the absence of unrecorded cross edges.

## N04: Whole closed packet irreducibility and homomorphism-embedding restrictions

Each full regular G-packet is one-generated under the named unary translations. In a proposed free decomposition into proper closed substructures, the side containing a generator contains the whole packet; hence that packet is irreducible.

If two distinct packets have a recorded edge, their union is irreducible: closures force each whole packet into one side, and the edge forbids separating the packets between free sides. Apply the DEFINITION of homomorphism-embedding to these two types of closed irreducible substructures.

The restriction embeds each whole packet and each recorded two-packet union, preserving complete unary function-value sets (equality, not inclusion), literal fine records and owner labels according to ONE global language component. No assertion of global injectivity on two UNRECORDED packets is made.

After tree realization, a recorded non-F edge also prevents the two packet images from lying in the same actual F-class.

## N05: One global local-tree language normalization

Given f=(gamma,f_V):P->D, compose with (gamma^-1,id):D->gamma^-1 D. The composite has identity language component and the same vertex map. Relabel the WHOLE target tree with gamma^-1, including every constituent source copy and every overlap. Free amalgamation commutes with global relabelling, and gamma^-1 times any permitted relabelling remains in Gamma.

The normalized map is still a homomorphism-embedding, because the final map is an isomorphism. Every irreducible restriction retains its embedding property. Fine symbols and t_g were fixed all along; owner predicates now agree LITERALLY before any protected-base alignment. Do not normalize individual copies by unrelated language components.

## N06: Protected irreducible base, root choice and actual injectivization

Take a functionally closed induced C≤B0 with |C|≤n. E02 supplies a single map
f=(gamma,f_V):C→D. The same gamma applies on EVERY packet and every recorded
pair; there is no separate language choice on different tree nodes.

An A-copy in the Gamma_L category becomes, in the literal owner signature, a
Gamma-relabeled A-copy after choosing its vertex identification. Because Gamma
fixes binary colours and translations, the only possible literal discrepancy
between such copies is their owner names. Free amalgamation identifies actual
matching names on overlaps; it does not permit inconsistent owner labels at a
shared vertex.

Compose f with (gamma^{-1},id):D→gamma^{-1}D. This gives
(id,f_V):C→gamma^{-1}D, still a homomorphism-embedding. Apply the SAME relabel
to the whole tree construction. Every resulting node is still a permitted
Gamma relabel of A, overlaps remain closed, and the tree incidence pattern is
unchanged. This is exactly the source's HLN identity. It uses a genuine group
inverse, not a section or an independent choice at each node.

Observation 9.3 is applicable to a protected COMPLETE full-packet base A_*:
its image under f is an irreducible substructure of D because f restricts to
an embedding there. The image lies inside one source node. Proposition 9.2's
sequential tree construction can start at that node; the proof of 9.2
explicitly permits that choice. Realize the chosen node in N_B, use
named-owner homogeneity to align the embedded A_* with its prescribed copy,
and only then attach other nodes over complete closed overlaps by closed SAP.
No later language relabel is permitted after that base alignment.

Let P consist of k distinct literal regular packets with exactly one owner per point and whole recorded non-F matrices. Suppose the external local map f:P->D exists.

First normalize its global language component as in section 6. If a complete full-packet base A_* is protected, f(A_*) is irreducible and lies inside ONE constituent source copy by the external free-tree irreducible-piece property. Realize that source copy in N_B and use actual named-owner homogeneity to send its induced f(A_*) to the prescribed A_* pointwise according to the original formal vertex correspondence. Then realize the entire tree by T03 with that whole source copy fixed. If A_* is empty, skip this alignment.

The composite q:P->N_B preserves literal owners/functions/records and is injective on each packet and recorded pair, by section 5. In particular each packet maps ONTO one actual full F-packet, and each recorded adjacent pair maps into different actual packets. The protected base is already its prescribed embedding.

Invoke B025 lem:packet-collision (C27–C29) on q. It separates ONLY unrecorded packet collisions, keeping every protected base value and all recorded neighbour matrices, and yields an injective q'. Pull the complete actual structure back to P's original vertex set. This is a completion of P, not an embedding reflecting absence of records.

## N07: Actual vertex locality and complete induced chord data

For a specified simple origin cycle on k DISTINCT packet indices p_1,...,p_k, take the full function closure P_C of those k selected origins. Regularity/disjointness gives EXACTLY k|G| actual vertices. P_C is the full INDUCED PARTIAL structure on those packets. It includes every recorded chord between nonconsecutive cycle packets and its entire |G|^2 matrix.

If k|G|<=n, apply ONE external local tree map to this entire P_C. Section 7 yields an injective same-vertex completion preserving ALL records, including every chord. Its origins form a realization in the actual origin age, hence a typed cycle realization in U_B through the supplied age identification.

This argument does not assert the k unclosed origins themselves form an HKN substructure. It never drops a chord to force a desired cycle decomposition.

## N08: Recover total regular packets, owners and all-or-nothing matrices

These are local deductions, to be included as proved CCO application claims,
rather than hidden in E01/E02.

For v∈B0, its unary closure Cl(v) is irreducible: in a purported free split,
the side containing v must contain all its unary-function descendants and
hence all Cl(v). Irreducible faithfulness moves this WHOLE CLOSED structure
into literal A. Equality of full function-value sets under that embedding
forces total singleton t_g values and all regular group equations. Its image
is the one regular source packet generated by the image of v. Thus the
one-generated closures partition B0 into literal regular G-packets, and every
point has exactly one owner label.

Do not describe {v} alone as a unary-function substructure unless it is closed.
The source phrase “singleton irreducible faithfulness” should be read via the
one-generated closure; the module should use that precise formulation.

If a recorded edge joins two different packets, their UNION is irreducible:
the unary closures cannot be split, and the displayed cross relation prevents
putting the packets on opposite sides of a free split. Faithfulness embeds
that full two-packet induced structure into A. Since its two function orbits
are distinct, their images are distinct source F-classes, all binary colours
are outside F, and every entry of the |G|×|G| matrix is present with the actual
thin law. Binary names are fixed by the language component. Conversely, if no
cross relation is present, that pair stays a hole. This proves the
all-or-nothing recorded-matrix condition.

On one packet or a recorded two-packet union, a local homomorphism-embedding
is an embedding and hence injective with exact unary outputs. It need not be
injective on TWO UNRECORDED packets. Global injectivization is the separate
B025 packet-collision argument, not an HKN conclusion.

## N09: Assemble whole-origin completion and retain the partial reservoir

### R01 Requests and source irreducibility

A is complete, so it is irreducible. There are finitely many relevant requests because A, the language and Gamma are finite. An original fine partial map p with domain/range INSIDE A and compatible gamma extends over its G-saturated domain by
  p_hat(t_g x)=t_g p(x).
This is well-defined since p preserves actual thin colours relating two domain points in the same packet, and regularity gives unique relative phase. It preserves all fine records by the thin transport law, owners by actual Gamma/G compatibility, and total t_g equations. This is a partial Gamma-automorphism of A on closed domain/range.

For empty real domain, retain EVERY language component gamma. The empty vertex map with that language action is a genuine partial Gamma-map; no packet saturation erases gamma.

### R02 Invoke the named external provider

With n>=b|G|, obtain finite B0 containing A, extending all required partial Gamma-maps, irreducible-faithful and satisfying the exact local tree property. No packet/completion axioms are presumed of this unrestricted output.

### R03 Recover total regular packets from closed one-generated pieces

For v in B0 take its full unary closure Cl(v). It is irreducible: any free decomposition must place v on one side and therefore all of its closure on that side. Faithfulness maps Cl(v) by a global Gamma-automorphism into A as an induced closed substructure. Full function-value reflection, not mere homomorphism preservation, transfers from A:
- each t_g is defined and singleton-valued;
- t_0(v)=v and t_g t_h(v)=t_(g+h)(v);
- all t_g(v) are distinct for distinct g;
- the closure is exactly the regular orbit of v, of size |G|.

Thus all one-generated closures are regular packets. The transferred group equations imply they partition B0: two intersecting orbits coincide. Each point has exactly one owner label because its CLOSED PACKET maps into A, whose points do. This is the correction to the source's loose “singleton irreducible faithfulness” phrase.

The faithful closed packet also recovers its entire correct internal thin colour diagram.

### R04 Recover all-or-nothing fine matrices

If any fine binary edge joins two distinct recovered packets, their union is irreducible by section 5. Faithfulness sends the entire union into A. Its images are distinct full packets (embedding plus regular functions), so every cross colour is outside F. Reflection/completeness in the source A forces all |G|^2 fine edges to be present, with exactly the actual matrix
  col(t_g o_i,t_h o_j)=(g+h)c_ij.
No contradictory extra colour, missing matrix entry or thin cross edge can survive. If no cross edge is present, the pair remains unrecorded. This gives the exact all-or-nothing record condition before locality is used.

### R05 Short and long origin cycles

Choose arbitrary origins in the recovered packets; no equivariance is needed. For each simple specified origin cycle of size k<=b, apply section 8 since its packet closure has k|G|<=b|G|<=n vertices. This realizes the cycle in the actual origin age. Every longer simple cycle is automatically realizable by L05.

Hence EVERY specified simple cycle of the ENTIRE origin partial diagram has a typed homomorphic completion. This conclusion concerns all records of the whole partial graph, not only isolated cycle pictures.

### R06 One whole origin completion, packet restoration and A alignment

Invoke actual semantic CCO and B025 packet-separated injective completion for the entire origin diagram (C31/C33). The resulting origins lie in distinct actual packets with prescribed owners and recorded colours. Inflate by B025 lem:packet-origins to restore every full packet and recorded matrix. This gives an injective complete actual realization of ALL B0.

The image of the original A is complete, fine-colour/function/owner isomorphic to its prescribed actual copy by the original formal point correspondence. Named-owner homogeneity (C24) extends that inverse finite isomorphism, aligning the whole completion pointwise on A. Do not infer this alignment or a phase from owner labels alone; owner stabilizers may be nontrivial.

### R07 Structural output remains partial

The certificate C0 only fills missing colours for purposes of existence. B0 itself retains its original partial records, HKN automorphisms and irreducible faithfulness. Thus all requested partial maps still extend structurally on B0. No invariant choice of the extra completion colours, second valued HKN stage, safe selector or EPPA of the actual source is required by this local theorem.

The HKN size parameter counts actual vertices. A simple origin cycle with k
distinct packet indices generates a CLOSED induced partial structure with
exactly k|G| vertices. Include EVERY recorded chord and its entire matrix.
For k≤b this lies within n=b|G|, so the one local map applies to that complete
induced partial packet structure.

HKN alone gives neither an actual completion of this packet structure in N_B,
nor injectivity on its unrecorded packets. Those conclusions require the
global-language normalization, actual tree realization using closed SAP, and
packet-collision separation. After short-cycle completion, long-cycle locality,
typed semantic CCO, origin inflation and actual owner homogeneity yield the
whole reservoir's injective completion. The arbitrary completion certificate
need not be equivariant and its unrecorded colours must not be installed as
permanent HKN records.

Thus E01+E02 provide precisely the external structural input claimed by the
local manuscript. They do NOT by themselves prove thm:completable-reservoir,
ordinary EPPA of the final CCO source, safe palettes, or the global rank
assembly. No external applicability blocker was found in this bounded audit.

## Implementation boundary: reuse the proved general HKN library

The reusable general API actually exists in the user's completed repository:
https://github.com/shulda/lean_all_those_eppa_classes

Pinned inspected HEAD:
cd358cde844d5419fd43f30c441511927e09142f.

Files read directly:
- AllThoseEPPA/MainTheorems.lean
- AllThoseEPPA/TreeLikeUnrestrictedMaintree.lean
- MAIN_THEOREMS_API.md
- docs/wiki/Published-statements.md
- lean-toolchain and lake-manifest.json

Supported import:
    import AllThoseEPPA.MainTheorems

Exact declarations:
- AllThoseEPPA.MainTheorems.unrestrictedFaithfulCoherentEPPA
- AllThoseEPPA.MainTheorems.restrictedLocallyTreeLikeEPPA
- implementation: AllThoseEPPA.TreeLike.restrictedEPPA_from_any_witness

The inspected restricted declaration explicitly returns finite B, an exact
Gamma embedding of A, ordinary EPPA, irreducible-structure faithfulness, a
global homomorphism-embedding back to the old witness, and for EVERY closed
S with S.ncard≤n a homomorphism-embedding of its induced structure into an
actual TreeLike.TreeAmalgamation of FULL A-copies. Conditional coherence is
retained. It is stronger than the printed version by allowing n=0 and not
requiring A irreducible. The implementation adds/forgets a fresh binary
complete relation around the verified fixed-E construction; it does not
replace source copies by an arbitrary clique cover.

Current main CI evidence inspected:
- https://github.com/shulda/lean_all_those_eppa_classes/actions/runs/39040857889
- https://github.com/shulda/lean_all_those_eppa_classes/actions/runs/39040857833
Both report success on exact HEAD cd358cde.

Lean version is v4.34.1. The resolved mathlib SHA is
d13f23b723b8a846827a245b89c10fc7d3f11612, identical to the current lean_cco
pin. No known toolchain mismatch was found.

Remaining receiving obligations are the CCO-language singleton/set-valued
encoding, the actual Gamma symbol action, exact morphism/closure equivalence,
distinguished embedding normalization, and transport of the CCO packet
structure into/out of this API. No dependency was added, no other repository
was changed, and no fresh Lean consumer build or axiom audit was run here.
Therefore B027 must mark the external mathematical provider explicit and the
LOCAL LEAN ADAPTER as pending, while directing the receiving project to reuse
these existing proved main theorems rather than reprove HKN.

## 8. Verdict and immediate next step

The external theorem application is mathematically sound in the inspected
finite signature, with one global language component, full function-value
equality on irreducibles and all empty-domain requests retained. No additional
HKN hypothesis such as free amalgamation of the CCO age, a pre-existing
equivariant completion, faithfulness of the owner action, or an origin/group
section is needed.

Complete B027's LOCAL proof contracts separately: exact packet/closure
recovery, literal global normalization, closed-tree realization,
short-cycle locality with all chords, and full CCO completion. Keep E01/E02
as named external providers and the future Lean adapter visibly pending.

The existing general HKN declarations are read-only reusable candidates, NOT newly imported declarations in lean_cco. A receiving adapter must provide a finite singleton-output encoding of actual CCO functions, translate Gamma maps and closed induced substructures exactly, normalize the distinguished copy, and map the returned tree of FULL copies to the literal owner packet signature. E01/E02 remain published theorem nodes while this adapter is pending.

## Local algebra and source-premise firewall

A01 is the actual homogeneous finite typed SAP triangle source; A02 adds primitive individual sorts, and A03 adds semantic typed homomorphic CCO. The automaton and long-cycle profile arguments C01-C03 depend only on A01/A02, I01/I02 and the SAP edge-fixing injectivization provider I10. C04 alone adds CCO. In particular no S-amalgamation, safe selector or all-row decoder is used.

A04 is the supplied residual N_B closure/homogeneity/owner-lift/thin interface, retaining the original B025 normalization and current countability scope; A05 separately supplies CLOSED SAP. C05-C08 use actual closed bases, not full-real raw SAP. C09-C14 are finite unary/signature/map deductions conditional on their stated input data; they do not invoke either HKN existence theorem. C15-C19 are local source completion implications from a GIVEN local map. Only C22 onward obtains such maps and a witness via E01/E02.

The tree irreducible-piece property C14 is the elementary finite content of HKN Observation 9.3. For a tree split D=D1 amalgam_S D2, a closed irreducible K meeting both D1\S and D2\S would equal the free amalgam of its closed intersections with D1,D2 over K intersect S: there is no cross relation or mixed unary output across a free split. Hence K lies in one side. Inductively K lies in one source node. Starting tree induction at that node is permitted by the finite tree rooting property (HKN Proposition 9.2). This is required before protecting f(A_*); no unproved arbitrary one-copy containment is inferred merely from relation preservation.

B025 collision/origin theorems and B026 absorption/positive powers are imported, not counted again as new results. Exactly seven new source labels and one HLN equation are exported. No unrecorded pair is made an HKN nonedge in a completed actual image; record-preserving completions only add colours. Owner stabilizers need not be trivial, phases are determined by actual origin correspondence and thin functions, and the final A alignment uses a full actual named-owner partial isomorphism.


### Final contract qualification

C04 bounds the LENGTH of each tested cycle, never the size of the ambient finite origin diagram. Its universal quantifier ranges over arbitrary finite diagrams. The local compiled HKN adapter remains pending; the existing pinned AllThoseEPPA declarations and matching toolchain are references to reuse, not already imported CCO proofs.


### Final audit: pre-matrix irreducibility and request signatures

C10 is deliberately proved before and without D05: any two disjoint CLOSED regular packets with even ONE recorded cross fine edge form an irreducible induced union. The cross edge need not yet be known nonthin; matrix completeness is not assumed. C26 applies this weaker-premise statement to recover the full matrix by faithfulness, avoiding a precondition cycle. In A07/D12 each original p is explicitly a partial ISOMORPHISM between induced complete fine-colour reducts inside A, including injectivity/reflection and own(p(x))=gamma own(x). G-saturation subsequently supplies closed functional domains; the inverse used in C20 is legitimate.


D10 now defines ONLY the numerical n=b|G|, independently of D05. Before C23 the unrestricted HKN output has no assumed packet/matrix axioms. C18 proves the later closed k|G| count using recovered or explicitly given regular input packets. C26 obtains the source matrix law from actual thin transport I08; I09 remains only the already-specified matrix input to origin inflation. The recovery firewall rejects D05 as an ancestor of C24–C26.
