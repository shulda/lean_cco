# Finite-index packets and exact-kernel normalization — proof notes

Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`. Human-expanded mathematical preparation for OTHER Lean projects, not Lean proofs. The human TeX is unchanged. Full contracts, actual source coverage and dependency firewalls are in `module.json`. No SAP, NR2 or owner groupoid is assumed.

## N01: Foundations, relative indices and finite-index closure

Use one actual inhabited transitive homogeneous original real source with a
finite complete symmetric binary orbital language. Actual equality is a
separate atom. Invariant relations are unions of actual old pair orbitals;
there are consequently finitely many invariant equivalences. Original
represented products are associative and commute, because the product is
invariant and symmetric whereas taking converse reverses its factors.
Thus the join of two invariant equivalences is their represented product.
Do not assume the full invariant lattice distributive or its members RAW
word-exact. These elementary facts need no CCO or SAP.

For J<=K define [K:J] as the number of J-classes in one K-class. It is
uniform: an original automorphism carrying one point to another carries
both its K-class and the partition into J-classes. The underlying source
is inhabited, so every such class-count is positive; equality endpoints
give index one. Transitivity also makes the size of a finite-class invariant
equivalence constant. A finite upper relative index makes all intermediate
class counts finite. For J<=K<=T with [T:J] finite, partitioning the
J-classes in a T-class by their containing K-class gives

    [T:J] = [T:K] [K:J].

Uniformity of the fibre size is essential; it follows from original
transitivity, not merely from the existence of abstract equivalences.
The identity includes J=K, K=T and J=T. The product of two positive
finite class counts is finite. In particular, a finite-class lower
equivalence together with finite relative index gives finite upper classes.

For later counts, record actual transposition for permuting equivalences.
For arbitrary invariant A,B and a fixed x, send a class of A meet B
inside B[x] to its containing A-class in (A join B)[x]. Injection follows
because two points in B[x] which are A-related are (A meet B)-related.
Surjection follows from A join B=B;A: every A-class in the join-class
meets B[x]. Thus

    [B:A meet B] = [A join B:A],

whenever these counts are interpreted as actual class cardinalities.
This numerical statement is not inferred merely from a modular lattice
isomorphism. It is the elementary class-bijection argument already prepared
in `parity_hasse`, independent of that module's Hasse theorem.

Fix J. If K_1,K_2>=J have finite indices q_1,q_2 over J, their join also
has finite index, at most q_1 q_2. To check the bound directly, choose one
representative y_l of each of the q_1 J-classes inside K_1[x]. Every point
z in (K_1 join K_2)[x] has a witness x K_1 y K_2 z. Replacing y by its
chosen J-representative does not change its K_2-class, since J<=K_2.
The possible J-classes of z therefore lie in the union of the J-class
sets of the finitely many K_2[y_l], each with q_2 members. This gives
the stated bound, without asserting that these sets are disjoint.

There are finitely many invariant equivalences and J itself is a candidate
of index one. The finite join of ALL K>=J with [K:J] finite therefore
still has finite index over J and is their greatest member. Define it as
Sigma(J). No infinite join or limiting argument is needed. In particular
J<=Sigma(J), and F=Sigma(Id) is the greatest finite-class original
invariant equivalence. F is not assumed exact.

Useful closure bookkeeping can be proved now. If J<=K has finite index,
then Sigma(J)=Sigma(K). Indeed, [Sigma(K):J] is finite by multiplying
the indices through K, so Sigma(K)<=Sigma(J). Conversely K<=Sigma(J)
by maximality, and [Sigma(J):K] is finite, so Sigma(J)<=Sigma(K).
Taking K=Sigma(J) gives idempotence. If monotonicity is wanted separately,
for J<=K and T=Sigma(J), the transposition count gives
[K join T:K]=[T:K meet T]<infinity, because J<=K meet T<=T and
[T:J] is finite. Hence T<=Sigma(K). None of these assertions uses
distributivity, Hasse parity or word-exactness.

## N02: Loop criterion, canonical core and packet interval

Add the original complete-diagram triangle-fullness contract
`lem:cco-triangle-fullness`, available under the standing AP+homomorphic-CCO
hypotheses. Only this explicit geometry law, not the later quotient/groupoid
machinery, is needed for the loop criterion. A diversity atom a is looped
when the actual triangle (a,a,a) is legal. Write Gamma(a) for the least
original invariant equivalence containing a; in general Gamma(a) need not
be RAW exact.

If a is looped and lies in K outside J, triangle fullness realises a
complete a-coloured graph of every finite positive size m. Its vertices
lie in one K-class and in pairwise different J-classes, since every pair
has the atom a disjoint from J. Uniformity of relative index, or alignment
of one vertex to a fixed point by transitivity, gives [K:J]>=m for every
m. Thus [K:J] is infinite.

Conversely assume one K-class contains infinitely many J-classes. Put
k=max(1,|D|), where D is the diversity palette. Choose only R_k(3) points
from pairwise distinct J-classes in that one K-class. Their complete graph
is coloured by old diversity atoms in K outside J. Finite triangle Ramsey
gives a monochromatic triangle, hence a looped atom in K outside J. No
infinite set of representatives or infinite Ramsey theorem is needed.
Equivalently, in the absence of such a looped atom, the relative index is
strictly less than R_k(3), and in particular finite.

Finite triangle Ramsey itself may reuse the elementary preparation in
`canonical_hull`: f_k(0)=1, f_k(t+1)=k f_k(t)+1 suffices. Starting from
f_k(k+1) vertices, successively choose k+1 pivots with monochromatic
outgoing candidate sets and retain one final vertex. Two pivot colours
agree, and those pivots with the final vertex form a monochromatic
triangle. k=1 gives three vertices. If the diversity palette is empty,
the inhabited complete source is a singleton; the max(1,|D|) convention
avoids any zero-colour Ramsey definition. This proves the loop criterion
entirely with finite combinatorics.

Define kappa(J) as the finite join of Gamma(a) for all looped diversity
atoms a<=J. An empty generating family has join Id. Clearly kappa(J)<=J
and it already contains every looped atom of J. The loop criterion gives
[J:kappa(J)] finite, so N01 yields Sigma(kappa(J))=Sigma(J).

If J<=K has finite index, the loop criterion says that J and K have
exactly the same looped atoms; hence kappa(J)=kappa(K). In particular
kappa(J)=kappa(Sigma(J)). If Sigma(L)=Sigma(J), applying this fact to
L<=Sigma(L) and J<=Sigma(J) gives kappa(L)=kappa(J). Therefore
kappa(J)<=L<=Sigma(J).

Conversely suppose kappa(J)<=L<=Sigma(J). The full interval
[Sigma(J):kappa(J)] is finite, by multiplication through J. Hence
[Sigma(J):L] and [L:kappa(J)] are finite. It follows that
Sigma(J)<=Sigma(L). For the reverse inclusion, the product
[Sigma(L):L][L:kappa(J)] is finite, so
Sigma(L)<=Sigma(kappa(J))=Sigma(J). Thus Sigma(L)=Sigma(J).
This reverse inclusion must be recorded: finite [Sigma(J):L] alone only
shows one direction. We have proved that the entire Sigma-packet is
exactly [kappa(J),Sigma(J)], with kappa(J) its unique least element.

For word exactness, take one looped atom a. A legal monochromatic triangle
and pair homogeneity give a<=a^2, and symmetry plus seriality give
Id<=a^2. Two-step backtracks make the even power chain increasing. The
finite old palette makes it stabilize at a positive even power R=a^(2N),
with N>=1. Equality of consecutive stabilized even powers implies equality
with all later even powers, including a^(4N), so R^2=R. It is symmetric,
contains Id and a, and is contained in Gamma(a). Therefore R=Gamma(a).
This is an actual positive atomic word profile, not a STRONG profile with
an invented diversity identity.

The finite join of these Gamma(a) is their represented product. Concatenating
the finitely many positive atomic words represents kappa(J) by one positive
word whenever its looped generating family is nonempty. A looped diversity
generator is itself nonidentity, so kappa(J)>Id implies that the family is
nonempty. Conversely an empty family gives kappa(J)=Id, represented by the
genuine empty word. Thus every core is full RAW exact, but the source's
positive-word assertion is made only when kappa(J)>Id. This argument needs
no RAW exact convolution/Helly theorem: products of word profiles are words
by concatenation. In particular it does not imply that J, F or Sigma(J)
is exact. When J has finite classes it contains no looped atom, so
kappa(J)=Id and its packet is [Id,F].

## N03: Minimal infinite cut and its actual exact quotient

Assume M is infinite. The finite full invariant lattice has Top as an
infinite-class member, so choose an inclusion-minimal infinite member E.
It may be Top. Do not impose E<Sigma(E): this is not a hypothesis of the
source construction. Put H=E meet F. Since F has finite classes, H has
finite classes and H<E.

N02 gives [E:kappa(E)] finite. If kappa(E) had finite classes, multiplying
that finite class size by this finite index would make E-classes finite.
Therefore kappa(E) has infinite classes. Minimality and kappa(E)<=E give
E=kappa(E). E>Id, so its RAW representation is a positive word by N02.
This proves exactly the core/exactness clause needed here, without using
any theorem about a still-to-be-constructed conditional-bijection groupoid.

Every proper invariant J<E has finite classes by minimality, hence J<=F
by N01 and therefore J<=H. Conversely H is proper below E, and every
J<=H lies below E. Thus

    [Id,E] = [Id,H] union {E}.

In particular H is the greatest proper invariant equivalence below E;
neither H nor the lower interval is assumed RAW exact or distributive.
If J<E and [E:J] were finite, finite J-classes and finite index would
again make E-classes finite. Hence E has no proper finite-index refinement.
For a strict finite-index interval J<K<=E, K cannot equal E; therefore
K<=H. The equality case J=K is not subject to this strict conclusion:
J=K=E has index one. If H=Id, the lower interval is just {Id}; if E=Top,
all conclusions remain valid. When M is finite there is no minimal infinite
cut to choose, so this branch is not instantiated.

The actual quotient-source clause is a SEPARATE imported theorem (retain the pinned provider's countability premise A05 here, as detailed in N06):
`thm:exact-sorts-source`, provided by `raw_exact`. Apply its exact contract
to the original source and the actual FULL RAW exact invariant equivalence
E just proved. The provider gives that M/E, in the complete binary language
of all actual quotient pair orbitals of the original action, is again
homogeneous, triangle-defined, AP and semantic homomorphic CCO, with the
logical quotient identity retained. The provider also carries the standing
countability and finite-language hypotheses when these are required for
its homogeneity proof. The elementary lattice/core arguments above do not
use countability. E=Top gives the legitimate singleton quotient.

Do not infer this quotient conclusion merely from invariance, from finite
index, or from the abstract lattice. It uses the RAW exact-quotient theorem;
it is not a claim about arbitrary nonexact quotients, arbitrary tuple
imaginaries, mixed-sort transitivity or coherent automorphism lifting. SAP
of the quotient is not asserted. The later crossing calculation can depend
only on the elementary minimality conclusions of this section, without
importing this quotient-source clause or its RAW Helly proof.

## N04: Crossing a minimal cut: intersection and index identities

Fix the elementary data E,H from N03. Let J<=K and [K:J]=q be finite.
Put I=E meet J and L=E meet K. Inside one L-class, send an I-class to
its containing J-class inside the encompassing K-class. This map is
well-defined. If two such points are J-related, they are also L-related
and hence E-related, so they are I-related. The map is injective, giving

    [L:I] <= [K:J] = q < infinity.

If I<L, then L cannot equal E: otherwise I<E would be a forbidden proper
finite-index refinement of E. Thus L<E and N03 gives L<=H. This conclusion
is conditional on I<L. When I=L=E, for instance E<=J, it is false in
general that L<=H, and no such conclusion is used.

For permuting equivalences, with J<=K, the modular identity is

    K meet (E join J) = J join (E meet K) = J join L.

An actual witness proof avoids assuming distributivity. If xKz and
x E y J z witness membership in the left side, J<=K gives yKz and
hence xKy. Thus x (E meet K) y J z, which lies in L join J. The
reverse inclusion is immediate from containment. The same calculation
with H in place of E gives K meet (H join J)=J join (K meet H).

If I=L then L<=J, and K meet H<=L<=J. Both J join L and
J join (K meet H) equal J. If I<L, the previous paragraph gives L<=H,
and H<=E implies K meet H=L. In either case

    K meet (E join J) = K meet (H join J).

This is the point where minimality of E is used. No exactness assumption
on E,H,J,K is needed for this intersection identity once the elementary
minimality hypotheses have been supplied.

The numerical identity has a stronger elementary scope: for ANY commuting
invariant E and J<=K of finite relative index, not necessarily a minimal
cut, set D=K meet (E join J)=J join L. Index multiplication through D
and the two actual class-transposition bijections of N01 give

    [K:J] = [K:D] [D:J],
    [K:D] = [E join K:E join J],
    [D:J] = [L:I] = [E meet K:E meet J].

The first transposition uses the pair K and E join J, whose join is
E join K and meet is D. The second uses J and L, whose join is D and
meet is I. Thus all factors are positive finite integers and

    [K:J] = [E join K:E join J] [E meet K:E meet J].

Equivalently, project the J-classes in K[x] to the (E join J)-classes
in (E join K)[x]. Every target class meets K[x] by permutability, so
the map is onto. Its fibres consist of the J-classes inside one D-class,
whose number is [D:J]=[L:I]. Original transitivity makes these fibre
sizes uniform. Either argument proves the actual numerical counts, not
just an abstract interval correspondence. If J=K, both factors are one.
If E<=J the meet factor is one; if K<=E the join factor is one. No
relative-index-two/Hasse result is used.

Finally take K=Sigma(J). Its index over J is finite by construction.
Before simplifying the right-hand intersection, prove F<=Sigma(J):
transposition gives

    [F join J:J] = [F:F meet J] <= [F:Id] < infinity.

Hence F join J<=Sigma(J), so H<=F<=Sigma(J), and of course J<=Sigma(J).
Apply the established intersection identity to this finite-index interval:

    Sigma(J) meet (E join J)
      = Sigma(J) meet (H join J)
      = H join J.

This is the claimed Sigma-crossing formula, including J=Top, J=Id and
E=Top where those choices satisfy the standing data. F need not be exact;
the finite class count is its only role in the absorption step. The entire
crossing branch uses represented permutability, class counts, finite-index
closure and elementary minimality, with no RAW exact Helly/CRT,
regularization, thin translation group or conditional groupoid input.

## N05: Finite square-kernel regularization

Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`; source result `lem:finite-regularization`. This stage concerns the actual original group action and equality-inclusive represented relations. It does not require a homogeneous/CCO quotient source.

The elementary assumptions suffice: an inhabited transitive original action with finitely many actual pair orbitals, all symmetric, an actual invariant equivalence F with finite real classes, and the original definition of full RAW exactness as nonempty finite intersections of represented atomic word profiles. In the source F is the greatest such equivalence, constructed earlier as Sigma(Id), but greatestness is unnecessary for the square construction itself. Homogeneity/completeness of the original source supply its identification of atomic colours with pair orbitals. No SAP, triangle fullness, CCO, exact-ball Helly, exact convolution or countability is used here.

List the diversity atoms below F as a_1,...,a_r; real equality is a separate atom. Every a_i is serial by original transitivity and nonemptiness, and symmetric, so Id is contained in a_i squared. Put P=a_1 squared;...;a_r squared, taking P=Id when r=0. All products are represented products. Since every factor contains Id, P contains Id and every individual a_i squared. It is invariant and hence symmetric because all original orbitals are symmetric. Also P is contained in F.

The powers P,P squared,... increase since Id is contained in P. There are finitely many orbital supports, so choose n>=1 with P^n=P^(n+1). Multiplication and induction then show P^k=P^n for every k>=n, and in particular H_0=P^n has H_0 squared=H_0. It is invariant, reflexive and symmetric, so it is an equivalence. It lies below F and has finite real classes. It is ONE actual atomic word profile (the empty word if r=0), hence full RAW exact without an exact-product theorem. Every a_i squared is contained in H_0.

For the quotient-thinness argument use only the original group G acting on the actual quotient Q=M/H_0. Name its actual G-pair orbitals. For each old atom a, equivariance sends its whole orbital to one quotient orbital b; conversely every quotient orbital occurs this way by choosing representatives. Its full old inverse image is H_0;a;H_0, by the elementary orbital-pullback law `lem:foundational-orbital-pullback`. A direct proof moves the quotient pair by one original automorphism and changes its two representatives within H_0-classes. This law needs no quotient homogeneity, CCO, exactness, joint lifting or section. It is an elementary B001 group-action contract.

Carefully distinguish the types: H_0;a;H_0 is generally a UNION of old atoms on M, and is the pullback of ONE orbital b on Q. It is not itself literally an old single atom. The source's wording that calls the saturated pullback an atomic quotient relation is shorthand for this correspondence.

For a below F, commutation of original invariant relations and idempotence of H_0 give

    (H_0;a;H_0)^2 = H_0;a^2;H_0 = H_0.

The final equality uses BOTH a squared contained in H_0 and Id contained in a squared. Old inverse image commutes with represented composition of quotient relations: an intermediate quotient class has a real representative, and full preimages are saturated. Equality of quotient relations is detected by inverse image because the quotient map is onto. Thus b squared is the actual diagonal of Q. The quotient orbital is symmetric. If two b-neighbours y,z of one point existed, symmetry would give y b x b z and hence y=z. Every quotient point has a neighbour by transitivity (also by b squared=Id). Therefore b is thin. If b is quotient equality, its map is the identity; equality is thin in this harmless extended sense, while the diversity definition concerns non-diagonal atoms.

The invariant quotient equivalence F/H_0 is defined on actual quotient classes. Every orbital below it has a representative old atom below F, because H_0 is contained in F. Consequently all its diversity orbitals are thin. No claim that Q is already a new homogeneous AP+CCO source has entered this argument.

If every diversity atom below F was thin, its symmetric unique-neighbour map is an involution and a_i squared=Id, so the constructed H_0 is Id. If some a_i is nonthin, choose two distinct a_i-neighbours of one point. Their pair belongs to a_i squared and is off the diagonal, so H_0>Id. This proves the advertised nontriviality alternative. Importantly, H_0=Id or thinness of F does NOT imply that there is no OTHER nonidentity finite-class exact kernel: this construction only absorbs the squares of atoms already inside F.

## N06: Palette-decreasing exact quotient normalization

This expands `lem:finite-exact-normalization-geometric`. Restore the standing symmetric original homogeneous finite complete binary AP+homomorphic-CCO source, with complete-diagram triangle fullness. This is the only stage here, apart from the earlier minimal-cut export's final quotient-source assertion, which needs the FULL exact-quotient SOURCE provider `thm:exact-sorts-source`.

Retain that provider's actual hypotheses. In the pinned source its route through `thm:typed-joint-exact-lifting` explicitly assumes a countable original source and uses countable back-and-forth. The elementary arguments of N05 and N07 do not need countability, but these notes do not remove it from the existing quotient-source theorem. A receiving project can instead take the precise quotient-source law conditionally; it must not silently promote an uncountable extension to an established provider.

At a current source M_i, if there is a nonidentity full RAW exact invariant equivalence K_i with finite real classes, take the ACTUAL quotient by K_i, naming all actual quotient pair orbitals. The full quotient-source provider supplies homogeneity, the relevant transitivity, symmetry, AP, triangle fullness and semantic homomorphic CCO in this language. The next step therefore has the same standing source interface. Countability persists because each quotient is the surjective image of the current countable carrier. K_i may be Top if the current source is finite; the quotient is then a singleton. No SAP preservation is asserted.

Termination uses an elementary orbital-count argument independently of the full source theorem. Each old pair orbital maps entirely to a single quotient pair orbital under the equivariant quotient map, and every quotient orbital has an old representative. Thus old atom names surject onto quotient atom names; quotient atoms cannot split an old orbital. The fibre over quotient equality contains original equality and at least one old diversity atom because K_i>Id. If the current diversity palette has size d_i, the total quotient atom count is therefore at most d_i, and its diversity count satisfies d_(i+1)<=d_i-1. This counts actual quotient orbitals, not arbitrary formal products or a freely declared quotient palette.

Induct on the natural-number diversity-palette size. Repeatedly choosing any available nonidentity finite-class exact kernel yields a finite chain of length at most the initial diversity count; no uniqueness or canonicity of choices is asserted. The zero-step chain is allowed. A singleton source has no nonidentity kernel and is already terminal. At termination no nonidentity finite-class full RAW exact invariant equivalence remains.

Construct the greatest finite-class invariant equivalence F_m in the terminal source using the earlier finite-index closure argument. If one of its diversity atoms were nonthin, N05 would produce a nonidentity full RAW exact equivalence H_0 below F_m, with finite classes, contrary to termination. Thus all atoms below F_m are thin. The implication used is exact-kernel-free implies thin bottom. Its converse is false and must not replace the stopping condition; N08 provides the source's explicit counterexample.

The first minimal-infinite-cut result earlier in this module requires the same full quotient-source provider ONLY for its final statement that M/E is a homogeneous triangle-defined AP+CCO source. Its exactness, lower-interval and no-finite-refinement parts have separate elementary/loop inputs. Regularization does not need that minimal-cut quotient conclusion, and no conditional groupoid, EPPA induction, owner lifting or arbitrary mixed quotient-source assertion is part of this normalization proof.

## N07: Thin-bottom translation group and transport

This expands `lem:thin-bottom`. Use the actual transitive original action with finite symmetric pair palette and an invariant finite-class equivalence F whose diversity atoms are all thin. These elementary assumptions suffice. CCO, SAP, triangle fullness, RAW exactness of F, regularization history and full quotient-source inheritance are not used.

For every atom q below F, including actual equality, let t_q(x) be the unique q-neighbour of x. Symmetry makes t_q an involutive permutation. Invariance and uniqueness give sigma(t_q(x))=t_q(sigma(x)) for every original automorphism sigma, so t_q is equivariant before it is known to preserve other colours. Do not declare it an automorphism at this point.

The composite of two such permutations is equivariant, and its graph is an invariant functional relation below F. It is a union of old pair orbitals. Every nonempty orbital is serial at every original point by transitivity, so a functional invariant relation cannot contain two different orbitals. Its graph is consequently exactly one old thin atom below F. Composition and inverse therefore give a finite group on these atoms, with identity the real equality atom. Every group element is involutive because its corresponding old atom is symmetric. A group of exponent two is abelian: (gh)^-1=h^-1 g^-1=hg, whereas (gh)^-1=gh. Thus it is an elementary abelian 2-group, written additively as G isomorphic to F2^d. For an elementary proof of the dimension statement, start with the trivial subgroup and, while it is proper, choose g outside it. The next generated subgroup is the disjoint union of H and gH, of twice its size; involutivity and commutativity identify it with H times C2. Finiteness terminates this process and gives G isomorphic to (C2)^d. No finite Hasse theorem is needed.

For each x, every y in F[x] has one unique old atom q_g from x, so y=t_g(x) for one unique g. The G-action is regular on each whole F-class, and |F[x]|=|G|=2^d. If F=Id, G is the trivial group and d=0. No packet origins have been chosen.

The map (x,y) -> (t_g(x),y) is an equivariant bijection of ordered-pair sets, hence takes an old orbital a to exactly one old orbital. Because t_g is involutive, its image relation is precisely q_g;a. Denote this one atom by g dot a. This includes the original identity atom. Original invariant relations commute, so switching the second endpoint gives a;q_h=q_h;a. Applying both switches gives

    col(t_g(x),t_h(y)) = (g+h) dot col(x,y).

This proof of the transport formula uses equivariance and the original relation algebra, not an assumption that t_g was already an automorphism. Taking h=g leaves every pair colour unchanged, since g+g=0. The bijection t_g thus preserves the complete original binary structure and is an actual automorphism. Its previously proved equivariance says that it commutes with every ambient automorphism; these translations form a central subgroup of Aut(M).

Do not strengthen the conclusion to a free action on the COLOUR palette. An external atom a can satisfy g dot a=a for nonzero g; in N08 all phase-forgetting r,c,b colours do so. Nor does regularity of each whole F-class provide a canonical origin in each class, a section of an owner-group homomorphism or coherent transport through arbitrary nonexact mixed quotients. These are distinct later obligations. A freely chosen set of packet representatives need not inherit the full regular action.

## N08: Subgroup lower intervals and the thin-not-exact-free source

For `cor:lower-subgroups`, first prove a purely elementary correspondence under N07. An invariant relation below F is a union of the graphs q_g. It is an equivalence exactly when the selected subset A of G contains 0, is closed under sums and is closed under inverses. Reflexivity, transitivity and symmetry give these conditions; conversely the subgroup conditions give an equivalence by the group composition law. Every selected subgroup supplies the whole literal atom union, so there are no additional invariant equivalences below F. This identifies [Id,F] with Sub(G) as an order/lattice isomorphism.

Suppose an inclusion-minimal infinite original invariant equivalence E exists and put H=E intersect F. Every proper invariant equivalence J<E has finite classes by minimality, hence J<=F by greatestness of F, and so J<=H. Conversely H has finite classes and is properly below E, so every subequivalence of H is a proper subequivalence of E. The correspondence above identifies H with a subgroup A<=G and gives

    [Id,E] isomorphic to Sub(A) with one additional greatest element E.

The notation Sub(H) in the source uses this identification; it is not a literal equality of a set of binary relations and a set of group subsets. E may equal Top. If H=Id, A is the trivial subgroup and this interval has just Id and E. The interval need not be distributive: subspace lattices of elementary abelian groups already contain nondistributive diamonds. This argument requires only the elementary proper-lower-interval part of `prop:minimalcut`, not its exact-quotient-source conclusion or its proof of E's exactness. It uses no CCO once its stated invariant-equivalence data are supplied.

Now audit `ex:thin-not-exact-free`. Let I,J be countably infinite and M=I times J times {0,1}. Name t within one cell between its two distinct points, r for equal I and different J, c for equal J and different I, and b for differences in both coordinates. The bit is invisible to r,c,b. All four are symmetric diversity atoms.

Finite partial isomorphisms preserve the two coordinate-equality patterns. Their induced partial maps of I and J extend to independent permutations. In each occupied cell the induced partial bit map extends independently to a permutation of its two points; combine these with the coordinate permutations. This proves transitivity and homogeneity, and hence actual age AP. For a complete triangle-legal diagram the row and column equality relations are equivalences. A common cell can contain at most two distinct formal vertices, because three would give the forbidden t,t,t triangle. Assign distinct coordinate names to its row and column classes and an injective two-point label in each cell. This realizes the diagram, proving triangle fullness. Boundary diagrams of at most two vertices are immediate.

For semantic homomorphic CCO, each edge imposes equality or inequality in I and separately in J. An inequality whose endpoints are connected by equality edges in one coordinate yields a shortest equality path plus that edge: a specified simple cycle with no homomorphism. The path has length at least two, because the same specified edge cannot require both equality and inequality in one coordinate. If every specified simple cycle maps, these two constraint systems are consistent. Assign fresh, distinct values to their equality components, independently for I and J.

The resulting forced cells are intersections of one I-equality component and one J-equality component. Each t-edge stays within a forced cell and requires its two bit labels to differ. The r,c,b edges impose no condition on bit labels. If the t-edge graph in a cell is not bipartite, a simple odd t-cycle is a specified simple-cycle obstruction: its coordinates are all forced equal along the cycle, while the two-element cell cannot realize an odd cycle. Conversely, if all these t-graphs are bipartite, choose their two-colourings independently and combine them with the solved coordinates. Different disconnected t-components may receive labels independently and unspecified vertices may coalesce. Every specified edge is preserved, proving CCO. Do not replace this argument with the Cartesian PHASE example's gain constraints on every edge: here only t sees the bit.

The greatest finite-class invariant equivalence is F=Id union t. Any other old diversity atom has infinitely many neighbours from each point, so any invariant equivalence containing it has infinite classes. Thus F is indeed greatest, not merely some finite equivalence. Its only diversity atom t is thin and t squared=Id. N05's canonical square regularizer is therefore H_0=Id.

Nevertheless let R be equality of the I-coordinate and C equality of the J-coordinate. Direct represented products give

    r squared = Id union t union r = R,
    c squared = Id union t union c = C,
    R intersect C = Id union t = F.

For example, for any endpoints in one row choose an intermediate column different from both endpoint columns; infinitude of J supplies it and gives two r-edges. The analogous choice proves the c calculation. Consequently R and C are full RAW exact positive word profiles, and F is a nonempty finite intersection of them, hence a NONIDENTITY finite-class full RAW exact kernel. Thin bottom therefore does not imply exact-kernel-free, even in this homogeneous triangle-defined AP+CCO source. The geometric normalization can first quotient by F; square-kernel regularization alone would stop too early.

The row equivalence E=R is a minimal infinite cut: any equivalence containing r contains r squared=R; containing c or b forces infinitely many points outside a fixed row. Its intersection with F is F. For x in one row and another row-owner, the c-neighbours in that target row are exactly the two points with x's J-coordinate. The conditional valency is two and

    E intersect c squared = R intersect C = F > Id.

After quotienting by F the target cell has one point and this particular valency becomes one. This verifies the source's diagnostic but does not establish the later conditional-bijection construction or any EPPA result. The independently prepared thin-bottom translation action is the global simultaneous cell flip; its palette action fixes r,c,b, illustrating the nonfree palette-action warning in N07.
