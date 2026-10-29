# B028 proof notes — orbit-safe matrices and one relative MI witness

Frozen source 490c3f36. Full local human proof expansions for exactly SIX newly selected results, with one OH auxiliary equation. This is a candidate preparation contract, not Lean, actual source-hypothesis certification or a global EPPA proof. B025 collision/origins, B026 safe-selector machinery, B027 reservoir and B024 rows/trim are reused rather than counted again. The normalized witness assumes ordinary EPPA ONLY for Age(Q/E), keeps the given finite coarse B witness/orbit/closure premises, and constructs every displayed fine-owner/local decoder input before its final use.

## N01: Exact source, local owner context and principal relative contract

Q is the actual normalized one-direction homogeneous symmetric-original source with finite thin regular group G, greatest finite-class equivalence F_Q, exact fine-owner equivalence E, residual R_E=F_Q, and ABSOLUTE real closure acl_Q(X)=F_Q[X] on finite sets.

U is a finite NONEMPTY actual G-closed set of E-owners; N_U is its entire real preimage. The existing named-owner source supplies:
- actual regular full G-packets, finite G, free/transitive G action on real packet vertices;
- possibly NONFREE/NONFAITHFUL induced action on owner labels;
- own(t_g x)=g own(x) and col(t_g x,t_h y)=(g+h)col(x,y);
- named-owner homogeneity and full-packet closed SAP in N_U;
- actual all-owner transversal with literal non-F palettes P_st and triangle-defined SAP+CCO primitive age;
- actual lifts for the permitted finite pure-owner group Gamma, which fixes literal fine atom names and commutes with thin owner translations. For moving readings require Gamma to contain the induced diagonal G action.

S is an ORIGINAL global raw fine-diversity subset. Its sole positive assumption at the outset is strong S-amalgamation over finite ABSOLUTE real acl_Q-closed spans in Q. Neither nonempty typed S^G nor all-span typed S^G-amalgamation is assumed before it is proved below.

All typed spans are spans of COMPLETE finite transversal structures with strong embeddings; arbitrary span is reduced to a common literal complete base by finite source isomorphisms. Origins/owner labels may repeat in type but formal transversal vertices are distinct.

## 2. Definitions

For a in P_st define
  a in S^G_st iff for EVERY g in G, g a in S.
The g=0 condition gives S^G_st subset S. For an actual non-F origin pair x,y of colours a, the full matrix has entries (g+h)a; since every r in G occurs as r+0, matrix-wide S-safety is EQUIVALENT to a in S^G_st.

Write real packet Pi=F_Q[x]={t_g x:g in G}. It has |G| distinct real vertices regardless of owner stabilizers.

An actual R07 packet is p=(i,f), not merely a structural index i. Distinct actual packets over the same i have different rows f. W# records matrices exactly over recorded structural pairs {i,j} with i!=j and has no record for any distinct actual packets over the same structural index.

Standing input Q is an INFINITE actual homogeneous transitive symmetric binary
AP+semantic-homomorphic-CCO source with finite actual orbital language. Retain
the current actual RAW/joint-quotient providers' countability scope when
instantiating them. Assume:
1. No nonidentity invariant finite-class FULL RAW EXACT equivalence.
2. Exactly ONE inclusion-minimal infinite equivalence E in the FULL invariant
   equivalence lattice. Its exactness is supplied by prop:minimalcut.
3. S_Q is a palette of ORIGINAL diversity atom names with strong amalgamation
   of finite ABSOLUTELY real-acl-closed induced spans. Empty base is included.
   The output amalgam can be closed subsequently. No arbitrary real SAP is
   assumed.
4. H is an actual invariant FULL RAW EXACT equivalence with E≤H.
5. Ordinary EPPA is assumed ONLY for Age(Q/E), not Age(Q), a rooted theorem on
   Q, or the same-rank owner master.

Let F=F_Q be the greatest finite-class invariant equivalence; it need not be
exact or identity. A0⊆Q is finite NONEMPTY. B⊆Q/H is finite induced with:
- pi_H(A0)⊆B;
- B is an ordinary EPPA witness for the projected A0;
- Gamma_B pi_H(A0)=B, where Gamma_B=Aut(B) in the FULL actual quotient language;
- B is closed under F_(Q/H), the greatest finite-class invariant equivalence
  of the actual quotient Q/H.

A request (p,gamma) consists of a PARTIAL ISOMORPHISM p:A0↝A0 of the original
complete fine-colour structure, gamma∈Gamma_B, and
  pi_H(p(x))=gamma pi_H(x) for all x∈dom(p).
Retain every (empty,gamma), including all nontrivial gamma. There are finitely
many such pairs.

Output: ONE finite induced D⊆Q, full-F-closed, containing F[A0], with
pi_H(D)=B, satisfying:
- each compatible (p,gamma) has an original-language automorphism beta of D
  extending p and inducing EXACTLY gamma on ALL B;
- for every nonempty all-non-S_Q clique Z⊆D and EVERY selected z∈Z, some
  relative automorphism alpha takes Z into F[A0] and z into A0.
The second clause may choose its owner component; it is not required to retain
a previously prescribed gamma. Coherence and a group section are not claimed.

The finite B EPPA premise is retained exactly as in the source. The local
construction below chiefly uses finite base/orbit/closure properties; do not
silently delete its EPPA clause merely because a narrower intermediate
construction does not inspect it.

## N02: Regular real-packet owner multiplicities and disjoint helper

Fix origin owner s. Real regularity gives a bijection g->t_g x from G to Pi, and own(t_g x)=g s. Consequently the owner labels in Pi are precisely Gs and each owner t in Gs occurs |Stab_G(s)| times. This is orbit-stabilizer for an action that is free on REAL points but not necessarily on owner labels.

For each G-orbit of U choose one actual packet whose origin has a representative owner s in that orbit. Its owner set is exactly that orbit. Packets chosen for different owner orbits cannot coincide, since one real packet only covers one owner orbit. The finite complete induced union contains a point of EVERY owner in U.

Given a finite actual full-packet closed old set V, use named-owner closed SAP over the empty closed base to amalgamate that complete helper union and V with disjoint images. Realize the resulting finite actual structure in N_U OVER V: if an arbitrary age embedding first moves V, named-owner homogeneity extends the inverse finite isomorphism of its complete V-image. The resulting helper T is a union of full packets disjoint from the prescribed actual V, with original literal owner labels unchanged.

No owner representative section, choice of a single distinguished point for each owner, G-action splitting or free owner action has been proved. One packet per owner orbit, not one packet per owner, is sufficient.

## N03: All-span orbit safety from ABSOLUTE closed-S amalgamation

### OS1 Inflate and align the typed span

Fix an arbitrary finite complete transversal span A->L,R. Inflate every vertex to its WHOLE F_Q-packet using the actual thin coordinates. A typed embedding of the origin base inflates uniquely by t_g a -> t_g e(a), retaining fine colours, owners and functions. Apply the existing actual named-owner full-packet closed-SAP provider to realize the two inflated complete factors strongly over the common inflated base F_Q[A].

Use actual N_U homogeneity to keep the prescribed complete old copy if needed. Restrict to the induced union V of the two factor images. It is a union of full actual F-classes and the two factors meet EXACTLY in the inflated base. No assumption about S is used by this preliminary placement.

### OS2 Add all-owner anchors, then form the absolute closed span

Use the helper from section 3 to adjoin T disjoint from V and meeting every fine owner of U. Work in the complete induced structure on V union T. Put
  C = F_Q[A] union T,
  L' = F_Q[L] union T,
  R' = F_Q[R] union T.
All are finite complete induced original-Q structures. Each is a union of full F_Q-classes, so the ABSOLUTE closure equation acl_Q=F_Q[-] makes it absolutely acl_Q-closed. Their actual intersection is exactly C.

This is the reason the original closed-S hypothesis applies. Relative acl_N-closedness alone would not discharge it; the absolute closure equation is essential.

### OS3 Original strong-S amalgam and literal owner restoration

Apply strong S-amalgamation to the original-language complete span L'<-C->R'. It gives an actual age amalgam with strong factor embeddings and every off-base cross pair coloured in S. Restrict to the union of factor images, which remains a union of full packets.

Embed that finite amalgam in Q and ALIGN its complete C-image to the prescribed original actual C by ORIGINAL Q homogeneity. This preserves all colours and the strong/S conclusions. Now each old point x of owner s has a fixed anchor t_s in T of that same actual E-class. Its fine relation to t_s lies in E and is preserved. Since t_s is the prescribed actual point, the new image of x has its original owner [x]_E=s.

This explicit base alignment is the missing implementation step behind the source phrase “each old vertex stays in its prescribed E-owner.” Merely having an abstract copy of owner anchors would preserve owners only up to an unspecified ambient quotient permutation.

### OS4 Strongness also forbids packet collision

A fine-colour embedding of a whole real F_Q-packet preserves every thin relation and therefore all definable t_g values. Its image has exactly |G| points and equals the WHOLE actual F_Q-class of its image origin. Thus two off-base packets from opposite factors cannot be distinct disjoint subsets of one target F-class: if they met that F-class they would both equal it, forcing off-base point identifications forbidden by strongness.

The new factor packets are consequently distinct actual F-classes, and selecting their original marked origins gives a STRONG typed transversal amalgam over A.

### OS5 Whole-matrix S-safety and derived nonemptiness

For new cross origins x,y and all g,h in G, the points t_g x,t_h y lie in opposite off-base factors and remain distinct. Original strong-S amalgamation therefore gives (g+h)col(x,y) in S. Taking h=0 for every g proves the origin colour belongs to S^G at its actual tags.

Hence S^G strongly amalgamates EVERY finite complete typed transversal span, including empty base. Taking two singleton factors with prescribed owner types s,t over empty A gives a non-F origin pair with colour in S^G_st, proving each typed palette NONEMPTY. Do not add nonemptiness as an earlier assumption.

### OS6 Translation, converse and pure-owner laws

For a in S^G_st and u in G, all g(ua)=(g+u)a are safe, hence ua in S^G_(us),t. Since u is involutive, this is an equality of transported palettes. Translating the second endpoint gives the same raw fine subset at types s,(ut); the actual endpoint law and diagonal colour-fixing thin action identify the two type presentations. Thus
  u S^G_st = S^G_(us),t = S^G_s,(ut)
with actual moved endpoint tags.

Typed converse fixes the literal symmetric old name and commutes with the thin action, so S^G is converse compatible. Genuine Gamma owner maps fix literal fine colours, commute with thin owner translations and transport P_st, so they preserve the tagged S^G. This is a pure owner statement, not an assertion that S itself is invariant under unilateral colour changes.

## N04: LOCAL parametric moving-reading extraction and safe-selector instance

Let h be ANY joint selector on original H satisfying:
conservativity, typed converse, survivor heredity, all-three-coordinate PC preservation, and pure-Gamma covariance. Assume the actual original-H algebra and endpoint switch laws used by B026. Define
  h^u_st(D) = u h_(us),t(uD).

The B026 C34–C39 proof uses only these axioms of h, not its particular gate construction:
1. Endpoint switches transport actual triangles and original exact profiles bijectively. Conservation and individual heredity follow by applying u, h, and u again.
2. Since diagonal u lies in Gamma, pure covariance identifies h_(us),t(uD) with h_s,(ut)(uD), giving converse and right-endpoint reading. Commutation with Gamma gives pure covariance. Expanding the definition gives switching h^(u+v)_(vs),t(vD)=v h^u_st(D).
3. For original exact D,A,P with D subset P*bar A and A subset bar D*P, put P'=P intersect(D*A). Atomic Peirce shows P' nonempty; supported-fork duplication and NONEMPTY-result original distribution give the two remaining PC inclusions. Switch the two outer endpoints by independent g,k, apply h to the transported PC triple, and undo the switches. This gives some c in P intersect(h^g(D)*h^k(A)).
4. For a chosen c=h^ell(P), use the two explicit Peirce rotations to obtain a=h^g(D) in {c}*bar A and b=h^k(A) in bar D*{c}. Original exact restrictions D'=D intersect({c}*bar A), A'=A intersect(bar D*{c}) contain those selected atoms. Survivor heredity keeps a,b. Duplication/distribution verify both singleton-c support inclusions; apply step 3 to (D',A',{c}) to get T(a,b,c).
Thus the parameters g,k,ell are fully independent.

This LOCAL B028 claim is a proof extraction/adaptation. Keep B026's existing C24 ordinary-selector export unchanged. Now instantiate h with h_(S^G) restricted to ORIGINAL H: B026 C27 provides every listed axiom on augmented K, so restriction supplies them on H. A conservative singleton output belongs to original H as a singleton. No equality with the separately chosen C24 ordinary selector is asserted.

B024's fixed decoder contract is then instantiated with THIS reading family, whose required axioms have now been supplied explicitly.

Let h be an ARBITRARY supplied selector with exactly D10's axioms. It is not defined here by any original gate procedure, and it need not equal B026's C24 h. The following argument uses the same actual original-H algebra/endpoint action as the inspected B026 proof, replacing every constructor reference by the D10 axiom actually used.

For an original exact D_st and u in G, a unilateral switch gives uD in H_(us),t; the same raw subset is in H_s,(ut). Apply u again to return to D. Thus conservation and heredity of h prove conservation and individual heredity of h^u_st(D)=u h_(us),t(uD). Diagonal owner u is in Gamma and fixes literal colours. Its pure covariance takes the moved pair (us,t) to (s,ut), proving h_(us),t(uD)=h_s,(ut)(uD). Combine this with converse of h for converse of h^u. Gamma commutation with G gives pure owner covariance. Expanding the moved first type proves
  h^(u+v)_(vs),t(vD)
    =(u+v)h_(us),t(uD)=v h^u_st(D),
using exponent two. Neither action faithfulness nor a frame/origin choice occurs.

Next take original exact D_st,A_tu,P_su with D subset P*bar A and A subset bar D*P. Let P'=P intersect(D*A). Choose d in D, then the first inclusion gives p in P,a in A with d in p*bar a. Atomic Peirce yields p in d*a, proving P' nonempty. Original exact closure makes P' exact. SAP-supported duplication gives D subset(D*A)*bar A and A subset bar D*(D*A). Since P' is nonempty, valid original meet-product distribution yields
  P'*bar A=(P*bar A) intersect((D*A)*bar A) contains D,
  bar D*P'=(bar D*P) intersect(bar D*(D*A)) contains A.
Thus PC(D,A,P'). Switch the two outer vertices independently by g,k. The new PC triple has types (gs,t,ku) and menus (gD,kA,(g+k)P'). D10 all-PC lets h select a legal triangle there. Undo those two endpoint switches. The selected first/second sides become h^g(D),h^k(A), using the proved right-endpoint expression, while the third atom lies in P' subset P. Therefore
  P intersect(h^g(D)*h^k(A)) is nonempty
for arbitrary independent g,k.

Now suppose PC(D,A,P), fix arbitrary independent g,k,ell, and put a=h^g(D),b=h^k(A),c=h^ell(P). Apply the preceding bilateral statement to the typed rotation (bar D:t->s,P:s->u,A:t->u), using g,ell. With converse of the readings it gives a0 in A such that T(a,a0,c). Apply it to (P:s->u,bar A:u->t,D:s->t), using ell,k, to get d0 in D with T(d0,b,c). Hence a in {c}*bar A and b in bar D*{c}.

Define original exact nonempty restrictions
  D'=D intersect({c}*bar A),
  A'=A intersect(bar D*{c}).
They contain a,b respectively, so INDIVIDUAL heredity of the fixed g/k readings gives h^g(D')=a and h^k(A')=b. For d in D', choose a0 in A with T(d,a0,c). Since d also belongs D, the same triangle shows a0 in bar D*{c}, hence a0 in A'. This proves D' subset {c}*bar A'. Conversely for a0 in A', choose its witness d in D; the same triangle puts d in D', proving A' subset bar D'*{c}. Apply bilateral support again to (D',A',{c}). Its conclusion {c} intersect(a*b) nonempty proves T(a,b,c).

This proves the full rectangular assertion for arbitrary supplied h and ALL independent g,k,ell, not merely shifts arising from a vertex potential and with NO equation g+k=ell. The menu variables and owner labels may coincide; the actual triangle vertices are still distinct. Every h-use has been listed as conservation, heredity, converse, all-PC or pure covariance, so the proof is genuinely parametric.

Only AFTER this local lemma, use C07/C08 and B026 C27 to construct h_(S^G) on augmented K. Its restriction to ORIGINAL H has all D10 axioms and keeps safe outputs whenever a menu meets S^G. Instantiate the local lemma with this restriction. A singleton output is original exact, so restriction causes no codomain problem. Existing B026 exports/constructor are unchanged, and there is no assertion that this safe h equals the ordinary h chosen in that module.

## N05: One preselected actual-packet PC family and universal safe decoder

Fix one finite R07 partial full-row packet universe W#, with actual packets p=(i,f), and one injective completion of its ORIGIN TRANSVERSAL in the actual typed SAP source. The fixed original PC initialization has recorded singleton {c_ij} over recorded structural pairs and full Top for every other actual pair, INCLUDING i=j with distinct rows.

### AR1 Recorded singleton matrices

The supplied injective completion gives an atomic solution surviving every update. Thus no domain empties, and a recorded singleton stays exactly {c_ij}. Its transported domain at endpoints z,w is the literal singleton {(z+w)c_ij}; EVERY conservative reading returns that atom, regardless of its parameter. The entire structural recorded matrix remains unchanged.

### AR2 Safe survivors on EVERY actual hole

Apply B026 safe-global-completion to the origin transversal, using the now-PROVED all-span strong palette S^G from section 4. It gives one record-preserving same-vertex certificate whose holes all lie in S^G. This certificate is not chosen equivariantly.

Every atom of that certificate survives every original PC update. Hence for EVERY originally unrecorded distinct actual packet pair p,q, including equal structural index i=j with f!=k,
  D_pq intersect S^G_(beta_i),(beta_j) != empty.
Original exactness and greatestness come from the original fixed-domain/PC provider.

This is a statement about ONE preselected final PC family on the ACTUAL packet set, not a different completion for each later request.

### AR3 Correct endpoint tags and all reading parameters

For arbitrary z,w in G,
  (z+w)D_pq intersects S^G_(z beta_i),(w beta_j).
Those types are individually shifted endpoints, NOT merely ((z+w)beta_i,beta_j). For every independent reading parameter u, move this exact menu by u at its first endpoint, use the safe selector on its nonempty moved S^G trace, and move back by u. Unilateral invariance gives
  h^u_(z beta_i),(w beta_j)((z+w)D_pq)
    in S^G_(z beta_i),(w beta_j).
The assertion is uniform over all u,z,w; it includes nonfaithful owner actions and repeated owner tags.

### AR4 Full translated matrices and universal decoder lifts

By the definition of S^G, every further translate (g+h)a of that output atom lies in ORIGINAL S. The B024 thin-switch decoder law says these are exactly the cross-matrix entries of the actual packet pair. Thus EVERY missing actual packet matrix is entirely original-S-safe, not merely its origin edge.

The local parametric claim in section 5 supplies all B024 reading hypotheses for h_(S^G)|H, including switching and independent triangles. The unchanged B024 proof yields one legal complete decoder, containing all original recorded matrices, on which EVERY structural reservoir automorphism with EVERY legal row correction acts as an original fine-colour automorphism.

The arbitrary injective certificate was used only to show nonempty/safe survivors; structural automorphisms are not required to preserve its unrecorded colours.

## 7. lem:orbit-safe-readings — source consequence

For original exact D meeting S^G_st and any u, the moved uD meets S^G_(us),t. Safe selection chooses there and translating back returns a colour in S^G_st subset S. This proves the pointwise assertion without a reservoir.

For a full-row reservoir, AR1–AR4 give the statement for all originally missing actual matrices, all row choices and every endpoint translate. Recorded matrices remain their old singletons. All structural maps/legal corrections act on the SAME decoder supplied by section 6, not on separately completed witnesses.

## N06: Unsafe multi-packet transport without a prescribed owner component

Input A+ is a finite complete full-packet source extending F_Q[A0] by DISTINCT fresh padding packets, every new cross matrix original-S-safe, including padding-to-original and padding-to-padding matrices. B0 contains A+ and has B027 irreducible faithfulness. Its fixed full-row decoder uses the section-6 safe readings.

Let Z be all-non-S and meet at least TWO actual packets.

### UT1 One actual row at each structural index

If Z met distinct packets (i,f),(i,k) over the SAME structural index, AR2–AR4 make every cross edge between those packets safe, contradiction. Thus each touched index i has ONE selected actual row f_i.

Similarly any two distinct touched indices must be structurally RECORDED, or their actual cross matrix would be safe. Consequently the touched index set J is a recorded clique, with |J|>=2.

### UT2 One structural HKN map on the WHOLE touched clique

Take the union of the FULL structural G-packets indexed by J. It is closed under all t_g, and every cross pair has its complete recorded matrix; internal packet records are complete as well. Thus the whole substructure is irreducible. Equivalently, any free split would have to keep each unary-generated packet in one side, and the recorded edge between every pair forbids separating packets.

Use irreducible faithfulness ONCE to get one structural Gamma automorphism s carrying this entire substructure into A+. No locality size bound on |J| or |Z| is needed. The real regular packet coordinates, not owner labels alone, give its unique form
  s(i,z)=(sigma i,z+b_i).
Owner stabilizers may be nontrivial.

### UT3 One legal simultaneous full-row correction

Invoke EXISTING B024 lem:acf-recorded-row-zeroing (C09,C25), not a new row-zeroing proof. Since J is a recorded clique and only one row f_i is chosen per i, the full-row compatibility criterion has no conflict. Its single correction matrix satisfies
  C_ij=f_i(j)+b_i for every selected i and EVERY j in I.
Recorded pairs and diagonals have no symmetry constraints; unrecorded pairs with one untouched endpoint are completed by the existing criterion.

For every selected packet,
  f'_i(sigma j)=f_i(j)+C_ij+b_i=0
at ALL coordinates, and the internal coordinate becomes z+b_i. Hence the entire actual packet is sent onto the zero row at sigma i, simultaneously for all i in J. The B024 universal lift makes alpha_C an automorphism of THIS same complete decoder.

This is clique transport with freely chosen structural owner component. It is not required to extend a separately prescribed source partial map or fix unrelated source zero rows.

### UT4 Padding is excluded after transport

The image alpha_C(Z) lies in the literal zero-row A+ and remains all-non-S because alpha_C preserves every original fine colour. It still meets at least two actual packets: alpha_C is a permutation commuting with all t_g and maps full packets bijectively.

If any point lay in a padding packet, choose another touched actual packet. The padding hypothesis makes their whole cross matrix safe whether the second packet is original or padding, contradiction. Hence
  alpha_C(Z) subset F_Q[A0].

The lemma does NOT select a specified root into A0, and does not treat a one-packet unsafe clique. Those are later invariant-trim/global-thin corrections already separated in B024/final MI assembly. It only supplies the multi-packet transport into the original full closure.

## N07: Normalized geometry, ONLY lower-quotient EPPA and FULL fine-owner group

E is exact by prop:minimalcut. If R_E!=F, the prepared global correspondence
dichotomy gives an infinite nonidentity exact C with E meet C=Id. Since the
FULL invariant lattice is finite, an infinite C contains some minimal infinite
direction. Uniqueness forces that direction to be E, hence E≤C, contradicting
E meet C=Id and E>Id. Therefore R_E=F.
Dependencies: minimalcut and global-correspondence, not EPPA or safety.

### M02 Absolute unary closure and real thin group

Use real_closure C11 directly to get acl_Q(A)=F[A] for all finite real A,
including A empty. Use normalization-geometric C25 for thin F and
thin-bottom C26–C28 for G. Naming a finite G-invariant fine-owner set later
uses the independently prepared harmless-owner/relative-closure proof.
Do not deduce absolute closure from closure only in N_U.

### M03 The finite list has actual ambient lifts before EPPA

Set U0=pi_E(F[A0]); it is finite and G-invariant. For each (p,gamma), use
nested-mixed with Id≤H to check p union gamma on dom(p) union ENTIRE B.
All mixed pairs are checked, including owner parameters outside pi_H(dom p).
Joint exact lifting yields ONE original automorphism sigma_(p,gamma) of Q.
Its restriction to F[dom p] induces a partial isomorphism
r_(p,gamma):pi_E(F[dom p])→pi_E(F[ran p]) of U0, compatible with gamma.
No ordinary EPPA of Q was used; empty p gives r empty with gamma retained.

### M04 Apply finite-base in the CORRECT lower quotient

Take X=Q/E, T=Q/H, pi:X→T. E≤H and actual exactness provide the actual
nested quotient language and its mixed recognizability. Each original sigma
from M03 induces an ambient automorphism of X realizing (r,gamma). Apply
lem:finite-base using ONLY ordinary EPPA of Age(X)=Age(Q/E).
Obtain ONE finite induced U1⊆pi^{-1}(B), containing U0 and onto B, and for
each request a selected alpha_(p,gamma)∈Aut(U1) with entire coarse action gamma.

This is a finite LIST construction. Neither the chosen ambient lifts nor the
selected extensions form a homomorphism or coherent section.

### M05 G-saturation creates no new COARSE owner

Put U=G[U1]. For kernel H, the old relation (F join H)/H has finite classes:
each reached H-class meets one finite F[x], since F;H=F join H.
Its invariant support is a union of actual quotient orbitals, so it is invariant
under FULL Aut(Q/H), not only the image of Aut(Q). Thus it lies below F_(Q/H)
(owner_action C07 with this kernel H).
For u∈U1 and any g∈G, choose x with pi_E(x)=u. Then t_g x∈F[x], so
  pi_H(t_g x)∈F_(Q/H)[pi_H(x)]⊆B.
Therefore U is finite, G-invariant and still lies precisely above B.
Surjectivity follows from U1⊆U and pi(U1)=B.
This is where the given coarse finite-class closure of B is essential.

### M06 Selected U1 maps extend to U via ORIGINAL joint lifting

For a selected alpha of U1 with prescribed gamma on ALL B, the joint map
alpha union gamma on U1 union B is a finite partial isomorphism of Q's actual
E/H quotient sorts. Nested-mixed checks every mixed pair. Joint exact lifting
in ORIGINAL Q supplies sigma. Since original automorphisms commute with each
t_g, sigma preserves G[U1] and restricts to alpha_hat∈Aut(U), extending alpha,
inducing the same gamma on B.
Do not assert centrality of G in an arbitrary full quotient automorphism group.

### M07 Use the FULL compatible fine-owner group

Define
  Gamma_tilde={alpha∈Aut(U): there exists gamma∈Gamma_B with
                            pi alpha=gamma pi on ALL U}.
Since U→B is onto, this gamma is unique; alpha↦gamma is a group homomorphism.
Take the full compatible group, not the subgroup generated by the finitely many
selected extensions. M06 puts every selected request lift into Gamma_tilde.
The empty original requests for EVERY gamma∈Gamma_B prove
Gamma_tilde→Gamma_B onto. No section is chosen.

### M08 Thin translations belong to and commute with ALL Gamma_tilde

G preserves U; its actual induced coarse translations preserve B by M05 and
are automorphisms of induced B. Thus rho_U(G)≤Gamma_tilde.
For EVERY alpha∈Gamma_tilde, with its unique coarse gamma, the joint finite
map alpha union gamma on ENTIRE U union B is a genuine actual E/H-sort partial
isomorphism. Lift it in Q. This original lift commutes with G, so
  alpha(g u)=g alpha(u) for all g∈G,u∈U.
This proves the needed commutation for the entire group, not merely selected
generators. The action rho_U may have a kernel.

## N08: Actual safe padding, complete source alignment and ONE fixed decoder

From M01/M02 and G-invariant U use B025 for N_U=pi_E^{-1}(U):
absolute/named closure F[-], actual owner homogeneity, closed full-packet SAP,
primitive full-owner transversal and inflation. Use the GIVEN absolute
strong closed-S_Q amalgamation and the B028-local orbit-safe-strong proof
to obtain all-finite-span strongly amalgamating S^G palettes on this transversal.
They are pure-Gamma_tilde covariant and invariant under unilateral thin
switches with moved types. Gamma_tilde ambient lifts from M08 preserve all old
fine names and functions, as required; no root frame is named.

### M10 Safe padding covers ENTIRE U

Choose an origin for each existing full packet in F[A0].
For a still-missing fine owner s∈U, strongly S^G-amalgamate the current complete
origin transversal with one fresh singleton of owner s over EMPTY base.
Realize in the actual transversal age and inflate the fresh origin to its whole
G-packet. Since U is G-closed, the entire packet remains over U. Align the old
full-packet factor via named-owner homogeneity so its REAL copy is retained.
Repeat at most |U| times.

The resulting finite actual complete full-packet Aplus⊆N_U contains F[A0],
realizes EVERY fine label in U, and every cross matrix involving a padding
packet is entirely ORIGINAL S_Q-safe. This includes padding-to-original and
padding-to-padding pairs. Nonfaithful owner action is allowed; one new packet
may cover an entire orbit with repeated labels, and must not be identified
with one owner label.

### M11 Lift p together with its ENTIRE fine-owner component

For each original request (p,gamma), choose the selected
gamma_tilde∈Gamma_tilde from M06. It extends the induced E-owner map of
F[dom p]; therefore p union gamma_tilde on dom(p) union ENTIRE U is a genuine
joint real/E-sort partial isomorphism. Use Id≤E mixed recognition and joint
exact lifting in Q. Restrict to F[dom p] to get the full-packet partial map
of Aplus, with range in F[A0], preserving original p and exact fine component
gamma_tilde. This is a new simultaneous joint lift, not an arbitrary extension
of p independent of the fine-owner action.

### M12 One structural reservoir contains ALL component requests

Apply B027 to this fixed Aplus, chosen finite list from M11, and EVERY
(empty,gamma_tilde) for gamma_tilde∈Gamma_tilde. Obtain one structural B0
with faithful source copies, all requested extensions and an injective
completion certificate in N_U fixing Aplus. The certificate may be completely
non-equivariant. Retain the external-HKN/local-Lean-adapter qualification of
B027. Its structural holes stay holes.

### M13 Choose the full-row decoder ONCE

Construct W={ (i,f,z): i∈I, f∈G^I, z∈G }. Actual packets are (i,f), not i.
The row-forgetting map to B0 and its completion is packetwise injective and
fixes zero-row Aplus; B024 packet collision separation gives one injective
origin certificate. Run greatest PC on actual packet indices ONCE. Use the
augmented S^G selector and its rectangular moving readings ONCE.

The B028 all-row interface then proves all originally recorded cross matrices
retain their old fine colours and EVERY originally unrecorded distinct actual
packet pair is entirely S_Q-safe, including equal structural indices with
different rows. This finite universe, its domains and its complete colouring
D0 are fixed before choosing any source-specific or clique-specific matrix C.

### M14 Actual N_U age and alignment of Aplus

Do not conclude membership in the actual Q/N_U age from an arbitrary abstract
triangle table. B024 proves legal three-packet and two-packet/thin triangles
and the entire thin matrix law. Use B025 C34's ACTUAL triangle-defined origin
age to realize one origin per packet in distinct real F-packets, then its full
inflation to realize all of D0 inside N_U. The zero-row Aplus is a complete
induced full-packet copy. Named-owner homogeneity (B025 C24) aligns this copy
with the prescribed actual Aplus. Transport the finite structure and all
automorphisms through this single owner-preserving alignment.

Thus the actual embedded D0 contains F[A0], has only coarse owners in B and
realizes ALL fine U. No choice of decoder is changed for individual maps.

### M15 Universal row lifts extend all prescribed source requests

For each structural extension from M12, B024's zero-row correction produces
a legal matrix C satisfying its touched rows, and its universal lift is an
automorphism of this SAME D0. It extends p on A0 and has exact
gamma_tilde on ENTIRE U, hence exact gamma on ENTIRE B. Source requests
include singletons and all empty-real-domain components. No arbitrary
structural map is assumed to preserve the reservoir's completion certificate.

## N09: IMAGE-group invariant trim, coarse support and selected roots

### M16 Multi-packet unsafe cliques transport into F[A0]

Use the separately proved multipacket transport provider on D0 and the padding
hypothesis of M10. Full-matrix safety forces an unsafe clique to meet at most
one actual packet per structural index; touched indices form a recorded
structural clique. Faithfulness moves their whole packet union into Aplus.
The one simultaneous row-zeroing correction maps those chosen rows to zero
rows in the fixed decoder. Safety of every padding cross matrix rules out
padding whenever at least two packets are touched. The result lies in F[A0].
No prescribed owner component is required for this clique-specific map.

### M17 K is a semilinear IMAGE group, not full Aut(D0)

Let K be the image of Aut_(Gamma_tilde)(D0) under forgetting its language
component and other auxiliaries. It is a subgroup of original-colour Aut(D0).
It contains the actual global thin G by B024 C27.
Because Aplus in zero rows realizes every s∈U, two semilinear automorphisms
with the same underlying permutation have equal owner action on every s.
Thus forgetting is an isomorphism ONTO K (B024 C31).
Do not claim K=FULL Aut(D0).

### M18 All empty fine requests give onto K→Gamma_tilde→Gamma_B

For every gamma_tilde∈Gamma_tilde, its empty structural extension from M12
and legal correction C=0 give an automorphism of the SAME fixed D0 with
that exact language component. Thus K→Gamma_tilde is onto, and M07 gives
the onto composite K→Gamma_B. This is why M12 includes ALL empty fine
requests, not only chosen lifts of coarse requests. A section is unnecessary.

### M19 Invariant trim preserves the full seed and all selected maps

Set
  D=union_{beta∈K} beta(F[A0]).
Reuse B024 C28: D is finite induced, full-F-closed and K-invariant, contains
F[A0], and all members of K restrict to original-language automorphisms of D.
Consequently every source extension in M15 and clique transport in M16
survives this SAME trim.

### M20 Exact coarse B survives; fine U support need not

The pi_H-image of D equals K pi_H(F[A0]). It contains
Gamma_B pi_H(A0)=B by M18 and the stated orbit coverage; it is contained in B
because D0⊆N_U and U projects precisely onto B. Therefore pi_H(D)=B.
This does NOT imply pi_E(D)=U. Padding can disappear from the trim.
Do not reuse fine full-support language faithfulness on D after trimming.
Coarse B-fullness is sufficient: two restricted maps with the same underlying
permutation agree on every coarse owner b, so their induced coarse component
is well-defined; each selected source extension still has its exact gamma.

### M21 Single-packet selected-root transport

If nonempty Z⊆D lies in one actual F-packet and z∈Z, write
z=beta(u) with beta∈K,u∈F[A0]. Then beta^{-1}(Z)⊆F[A0].
Choose a∈A0 in the packet of beta^{-1}(z). One global g∈G sends that point
to a and preserves ALL F[A0], packet by packet. Restrict g beta^{-1} to D.
This gives the selected-root conclusion without a clique assumption.

### M22 Multi-packet selected-root transport

For an unsafe Z meeting multiple packets, M16 gives delta∈K with
delta(Z)⊆F[A0]. Choose a∈A0 in the packet of delta(z) and one global g∈G
with g delta(z)=a. Since g preserves each packet, g delta(Z)⊆F[A0].
The restriction alpha=(g delta)|D is a relative automorphism with the desired
root. Its coarse component is allowed to change; no exact gamma is prescribed
in this transport clause. Independent permutations of separate packets are
neither used nor justified.

### M23 Forget auxiliaries with the original quotient map retained

After the single realization/alignment and trim, forget fine-owner names,
row/structural indices and unary translation symbols. D remains a finite
induced ORIGINAL-language substructure of Q. Every selected semilinear map
fixes literal original fine-colour names and hence is an original-language
automorphism. The ACTUAL recognizable quotient pi_H:D→B remains available
for later owner gluing, with each source extension's exact coarse gamma.
No same-rank rooted theorem or ordinary EPPA(Q) has been introduced.

## 4. Additional import/dependency firewalls for the module

- M01/M02 normalization/closure/thinness use no EPPA and no S_Q.
- M03 actual joint lifts use exact quotient geometry, not EPPA.
- M04 is the ONLY ordinary-EPPA consumer in this proof and its source is Q/E.
- M05 coarse owner preservation requires B's F_(Q/H)-closure; do not replace
  it by E-exactness alone or assume arbitrary B is G-stable.
- M08 proves commutation for EVERY compatible fine automorphism, not a
  generated subgroup or a speculative full global quotient action.
- Safe S^G/padding uses ABSOLUTE closure and all closed spans; named-owner
  finite closure alone does not license the original S_Q amalgamation.
- Original arbitrary S_Q need not be invariant under unilateral thin switches.
  That invariant palette is the full-matrix saturation S^G.
- Exact source-extension components and arbitrary clique-transport components
  are different conclusions with different quantifier orders.
- K is defined before trimming, using full fine U support in D0. The trim
  retains every coarse B but may lose fine U. Never replace K by full Aut(D0).
- HKN existence is still an explicitly named published dependency; current
  CCO encoding/normalization adapters in Lean remain uncompiled.
- All maps/corrections act on one finite fixed decoder; no second valued-HKN
  application or invariant completion certificate is required.

## 5. Verdict and feedback

No new mathematical gap or required source-statement repair was found in this
bounded normalized MI assembly. The following are necessary proof expansions
and should be recorded as FORMALIZATION_DETAIL:
- make exactness of E, residual R_E=F and ABSOLUTE unary closure explicit;
- apply finite-base to Q/E, with all simultaneous ambient lifts supplied FIRST;
- spell out (F_Q join H)/H≤F_(Q/H) before G-saturating U1;
- quantify the joint lift/commutation argument over ALL Gamma_tilde elements;
- align actual full-packet Aplus after the one decoder is realized;
- preserve IMAGE-K, coarse-B/full-fine-U distinction and unrestricted
  clique-transport owner component.

Recommended B028 package dependency spine is B002 (actual joint exact sorts),
B018 (finite-base subset of owner_action), B022 (global correspondence and
one-direction support), B024 (fixed decoder/trim), B025 (actual owner source),
B026 (safe selector/readings), B027 (reservoir), with thin/absolute closure
imports explicitly traced to B014/B011 as above. Package dependencies may
omit redundant ancestors if the actual selected claim DAG remains complete.
The whole global rooted/ordinary EPPA result remains source-relative.



## Actual module assembly and scope accounting

The names C01-C42 in module.json are canonical B028 IDs; OS/AR/UT and M/R identifiers inside the retained proof expansions are review-local milestones only. Their substance is selected explicitly in the module dependency graph. Exactly four complete orbit-safe source lemmas, one unsafe multipacket lemma and the normalized relative MI lemma are counted. Existing row zeroing (B024), packet helper/collision/closure (B025), augmented selectors (B026), and HKN (B027) are IMPORTS, not new source exports. Only OH is a new auxiliary equation.

A08 is a displayed local context for the standalone safe/interface theorems, not an unproved additional input to the principal construction. In C24-C29 the original principal source builds the actual finite G-invariant U, its entire compatible Gamma_tilde, and all original lifts. C30 FIRST constructs the B025 source context at these data without using S or any safe theorem; C31 THEN instantiates C07/C08 there using the given original strong closed-S premise and constructs Aplus; C33 constructs the structural B0; C34 constructs and fixes the full-row certificate/PC/decoder; C35 realizes it in N_U and aligns its COMPLETE source. Thus every use of a local conditional theorem at the final assembly has an earlier explicit constructor, and no local witness is assumed to exist without proof.

The arbitrary source S_Q need not be unilateral-G-invariant. The definition of S^G plus all-span strong amalgamation is what yields uniform full-matrix safety. All PC/colouring choices precede every source/clique correction; one never chooses a different decoded structure for each requested map. In unsafe transport, the structural source map may fail to preserve arbitrary HKN certificate holes, but its universal row lift preserves the fixed decoded fine colours.

Ordinary EPPA enters ONLY I03/C26 at X=Q/E, after E exactness/source inheritance and simultaneous actual ambient request lifts. I04 imports ONLY C07 from the larger owner provider, so no EPPA(Q) premise is acquired from unrelated claims. The finite B EPPA hypothesis is retained from the human statement even where narrower intermediate steps do not inspect it. Countability remains only in the current actual RAW/source specialization, not the finite support/row/group arguments. The final result is a local relative MI constructor under these exact inputs; finite exact restoration and global P/O/U rank assembly remain outside this module.

The explicit C30 source-context claim has NO dependency on S, SG, a selector or a decoder. This ensures all A08 source conditions are proved before the universally quantified local orbit-safe theorem C07 is applied at C31. The local conditional theorem is reused by substitution of the constructed U/Gamma_tilde/N_U; no source property is inferred from its later safe-completion conclusion.
