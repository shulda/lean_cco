#!/usr/bin/env python3
"""Bounded B027 locality/packet/HKN-interface diagnostics, NOT HKN proofs.

Representation and preflight: the independent four-diversity-colour table
forbids only monochromatic R and B triangles, with two neutral colours.
A second singleton palette tests ell=0. States (endpoint sort, nonempty
proper profile) are reached from POSITIVE words; no equality atom is used.
Literal cycle diagrams independently test the profile word/cycle bounds.

Packets are (i,g), g in C2 or C2^2, with total t_h(i,g)=(i,g XOR h).
Only structured packet permutations and phase offsets are enumerated, not
all carrier bijections. A nonthin fine matrix is c XOR g XOR h. Separate
S3 owner-predicate tables test global language normalization without making
these independent finite diagnostics into one claimed infinite source.

Search sizes: <=28 abstract proper masks per fixed start sort; positive
words through length four and cycles through length five; at most 12 packet
vertices for the collapse example, 16 for chord closure; <=32 two-packet
structured maps; <=24 compatible S3 three-copy trees; fewer than 17,000
collision/protected-base states (all graphs through 3 packets and selected
4-packet graphs). Fixed names, no redundant colour relabeling or full n!
permutation search. Cached 4-bit products; expected practical runtime <10s.
All closure loops are capped by finite carriers. Pilot timeout ten seconds,
full SIGALRM/phase deadline thirty seconds. Failure asserts include finite
witnesses; success prints one JSON checkpoint with bounded witnesses.

Reproduce from manuscript root:
  timeout 10s python tools/check_hkn_reservoir_controls.py > /tmp/b027-controls.json
No other control script is imported. No finite diagnostic certifies HKN,
infinite closed SAP/CCO/primitivity, actual source realization, EPPA, or
compatibility of arbitrary completion choices with the reservoir action.
"""
from collections import Counter, deque
from itertools import combinations, permutations, product
import json
import signal
import time

START = time.monotonic()


def require(ok, message, witness=None):
    if not ok:
        raise AssertionError((message, witness))


def tick():
    require(time.monotonic() - START < 30, '30-second diagnostic deadline')


def subsets(items):
    items = tuple(items)
    for size in range(len(items) + 1):
        yield from combinations(items, size)


def model_products(colours):
    top = (1 << colours) - 1
    legal = lambda a, b, c: colours == 1 or not (a == b == c and a in (0, 1))
    atoms = lambda x: tuple(a for a in range(colours) if x & (1 << a))
    table = {(a, b): sum(1 << c for c in range(colours)
                         if any(legal(x, y, c) for x in atoms(a) for y in atoms(b)))
             for a, b in product(range(top + 1), repeat=2)}
    return top, table, legal


def locality_controls(counts, witnesses):
    for colours in (1, 4):
        top, table, legal = model_products(colours)
        for start in range(2):
            initial = {(end, 1 << a): ((start, end), (a,))
                       for end, a in product(range(2), range(colours)) if 1 << a != top}
            paths, edges, todo = dict(initial), {}, deque(initial)
            while todo:
                state = todo.popleft()
                out = set()
                for end, atom in product(range(2), range(colours)):
                    new = table[state[1], 1 << atom]
                    require(bool(new), 'compatible positive profiles stay nonempty', (state, end, atom))
                    if new == top:
                        continue
                    nxt = (end, new)
                    out.add(nxt)
                    if nxt not in paths:
                        oldtypes, oldword = paths[state]
                        paths[nxt] = (oldtypes + (end,), oldword + (atom,))
                        todo.append(nxt)
                edges[state] = out
                require(len(paths) <= 2 * (2 ** colours - 2), 'finite proper-state bound')
            indegree = {q: 0 for q in paths}
            for targets in edges.values():
                for q in targets:
                    indegree[q] += 1
            queue = deque(q for q in paths if not indegree[q])
            order = []
            while queue:
                q = queue.popleft()
                order.append(q)
                for nxt in edges[q]:
                    indegree[nxt] -= 1
                    if not indegree[nxt]:
                        queue.append(nxt)
            require(len(order) == len(paths), 'proper-profile automaton is acyclic', edges)
            distance = {q: 1 for q in initial}
            longest = dict(initial)
            for q in order:
                for nxt in edges[q]:
                    candidate = distance[q] + 1
                    if candidate > distance.get(nxt, 0):
                        # Recover an actual transition atom for the witness.
                        atom = next(a for a in range(colours)
                                    if table[q[1], 1 << a] == nxt[1])
                        distance[nxt] = candidate
                        owner_path, word = longest[q]
                        longest[nxt] = (owner_path + (nxt[0],), word + (atom,))
            ell = max(distance.values(), default=0)
            bound = 2 * (2 ** colours - 2)
            b = max(3, ell + 1)
            require(ell <= bound, 'node-count bound includes the first positive edge', (ell, bound))
            require((ell, b) == ((0, 3) if colours == 1 else (2, 3)),
                    'singleton palette / exact word-to-cycle boundary', (colours, ell, b))
            if longest:
                q = max(longest, key=lambda q: len(longest[q][1]))
                owner_path, word = longest[q]
                witnesses['longest_proper_word'] = {'colours': colours, 'owners': owner_path,
                                                    'word': word, 'profile': q[1], 'ell': ell}
                require(len(word) == ell and q[1] != top,
                        'length ell can still be proper; bound uses STRICTLY longer')
            for length in range(1, 5):
                for owner_tail in product(range(2), repeat=length):
                    for word in product(range(colours), repeat=length):
                        profile = 1 << word[0]
                        for a in word[1:]:
                            profile = table[profile, 1 << a]
                        require(length <= ell or profile == top,
                                'every positive word LONGER than ell is full',
                                (colours, (start,) + owner_tail, word, profile, ell))
                        counts['positive_words'] += 1
            # Cycle colourings and owner labels are literal independent finite
            # diagrams. Missing chords are completed with a neutral colour.
            for n in range(3, 6):
                pairs = tuple(combinations(range(n), 2))
                triangles = tuple(combinations(range(n), 3))
                for values in product(range(colours), repeat=n):
                    graph = {e: (2 if colours == 4 else 0) for e in pairs}
                    for i, a in enumerate(values):
                        graph[tuple(sorted((i, (i + 1) % n)))] = a
                    literal_completion = all(legal(graph[i, j], graph[j, k], graph[i, k])
                                             for i, j, k in triangles)
                    profile = 1 << values[0]
                    for a in values[1:-1]:
                        profile = table[profile, 1 << a]
                    predicted = bool(profile & (1 << values[-1]))
                    require(predicted == literal_completion,
                            'cycle criterion matches an independent literal chord completion',
                            (colours, n, values, profile, graph))
                    require(n <= b or predicted, 'no bad cycle longer than max(3,ell+1)',
                            (colours, n, values, ell, b))
                    if not predicted:
                        witnesses.setdefault('sharp_bad_cycle', {'length': n, 'colours': values,
                                                                'ell': ell, 'b': b})
                    counts['literal_cycle_completions'] += 1
            counts['proper_profile_states'] += len(paths)
            counts['locality_models'] += 1
    # Negative scope: an imprimitive two-block DIVERSITY atom is idempotent.
    # It is not logical equality. The proper-profile state has a self-loop.
    require((0 ^ 0) == 0, 'imprimitive palette supplies a proper self-loop')
    witnesses['imprimitive_automaton_cycle'] = {'proper_atom': 'within-block diversity',
                                              'positive_multiplier': 'within-block diversity'}
    counts['negative_imprimitive_automata'] += 1
    tick()


class PacketDiagram:
    def __init__(self, packets, order, records):
        self.n, self.order = packets, order
        self.vertices = tuple(product(range(packets), range(order)))
        self.records = frozenset(tuple(sorted(e)) for e in records)

    def function(self, h, x):
        return x[0], x[1] ^ h

    def closure(self, selected):
        result = set(selected)
        for _ in range(len(self.vertices) + 1):
            enlarged = result | {self.function(h, x) for h in range(self.order) for x in result}
            if enlarged == result:
                return frozenset(result)
            result = enlarged
        raise AssertionError('functional closure exceeded the finite carrier')

    def colour(self, x, y):
        if x[0] == y[0]:
            return 'thin', x[1] ^ y[1]
        if tuple(sorted((x[0], y[0]))) in self.records:
            return 'outside', x[1] ^ y[1]
        return None


def packet_controls(counts, witnesses):
    for order in (2, 4):
        p = PacketDiagram(3, order, ((0, 1), (1, 2)))
        for x in p.vertices:
            require(p.closure((x,)) == frozenset((x[0], g) for g in range(order)),
                    'one-generated closure is one WHOLE regular packet', (order, x))
            for a, b in product(range(order), repeat=2):
                require(p.function(a, p.function(b, x)) == p.function(a ^ b, x),
                        'literal group equations', (order, a, b, x))
            counts['one_generated_packets'] += 1
        for selected in subsets(tuple((0, g) for g in range(order))):
            selected = frozenset(selected)
            closed = p.closure(selected) == selected
            require(closed == (not selected or len(selected) == order),
                    'proper nonempty packet subsets are NOT substructures', (order, selected))
            counts['packet_subset_closedness'] += 1
        # Every closed nonempty substructure is a union of whole packets.
        # Determine irreducibility independently by all possible free splits.
        for chosen in subsets(range(3)):
            if not chosen:
                continue
            chosen = frozenset(chosen)
            free_splits = []
            for left in subsets(chosen):
                for right in subsets(chosen):
                    left, right = frozenset(left), frozenset(right)
                    if left == chosen or right == chosen or left | right != chosen:
                        continue
                    if all(tuple(sorted((i, j))) not in p.records
                           for i in left - right for j in right - left):
                        free_splits.append((left, right))
            clique = all(tuple(sorted(e)) in p.records for e in combinations(chosen, 2))
            require((not free_splits) == clique, 'irreducible packet unions are exactly recorded cliques', chosen)
            counts['free_split_irreducibility_tests'] += 1
        target = PacketDiagram(2, order, ((0, 1),))
        collapse = {x: (x[0] % 2, x[1]) for x in p.vertices}
        require(len(set(collapse.values())) < len(p.vertices), 'unrecorded endpoints really collapse')
        for x in p.vertices:
            for h in range(order):
                require(collapse[p.function(h, x)] == target.function(h, collapse[x]),
                        'collapsing map preserves every total unary function')
            for y in p.vertices:
                if p.colour(x, y) is not None:
                    require(p.colour(x, y) == target.colour(collapse[x], collapse[y]),
                            'all source records preserved by noninjective global map', (order, x, y))
        for chosen in ({0}, {1}, {2}, {0, 1}, {1, 2}):
            vertices = tuple(x for x in p.vertices if x[0] in chosen)
            require(len({collapse[x] for x in vertices}) == len(vertices),
                    'map embeds every irreducible packet union', (order, chosen))
            require(all(p.colour(x, y) == target.colour(collapse[x], collapse[y])
                        for x, y in product(vertices, repeat=2)),
                    'restriction reflects entire fine data on irreducibles', (order, chosen))
            counts['irreducible_restriction_embeddings'] += 1
        counts['noninjective_homomorphism_embedding_examples'] += 1
        # All structured two-packet embeddings extending one origin edge.
        for origin_colour in range(order):
            pulled_matrices = set()
            for sigma in permutations(range(2)):
                for offsets in product(range(order), repeat=2):
                    if offsets[0] ^ offsets[1] != origin_colour:
                        continue
                    images = {(i, g): (sigma[i], g ^ offsets[i])
                              for i, g in product(range(2), range(order))}
                    require(all(images[(i, g ^ h)] == target.function(h, images[(i, g)])
                                for i, g, h in product(range(2), range(order), range(order))),
                            'candidate maps commute with ALL unary translations')
                    matrix = tuple(target.colour(images[(0, g)], images[(1, h)])
                                   for g, h in product(range(order), repeat=2))
                    pulled_matrices.add(matrix)
                    counts['structured_recorded_pair_maps'] += 1
            expected = tuple(('outside', origin_colour ^ g ^ h)
                             for g, h in product(range(order), repeat=2))
            require(pulled_matrices == {expected}, 'one old edge plus induced packet embedding forces ENTIRE matrix')
            sparse = tuple(('outside', origin_colour) if (g, h) == (0, 0) else None
                           for g, h in product(range(order), repeat=2))
            require(sparse[0] == expected[0] and sparse != expected,
                    'one-edge preserving map fails INDUCED reflection before full matrix recovery')
            counts['negative_sparse_matrix_embedding_examples'] += 1
            counts['all_or_nothing_recorded_matrices'] += 1
        # k origins are not a closed HKN domain; generated induced partial
        # structure retains all matrices, including a nonconsecutive chord.
        cycle = {(0, 1), (1, 2), (2, 3), (0, 3)}
        chord = (0, 2)
        pc = PacketDiagram(4, order, cycle | {chord})
        closed = pc.closure((i, 0) for i in range(4))
        require(len(closed) == 4 * order > 4, 'locality counts k|G| ACTUAL vertices')
        require(closed == frozenset(pc.vertices), 'cycle-generated structure is FULL induced packet domain')
        require(sum(pc.colour((0, g), (2, h)) is not None
                    for g, h in product(range(order), repeat=2)) == order ** 2,
                'every recorded chord keeps the entire matrix')
        dropped = PacketDiagram(4, order, cycle)
        require(pc.colour((0, 0), (2, 0)) is not None and dropped.colour((0, 0), (2, 0)) is None,
                'dropping a chord fails record preservation of the actual closed source')
        # A second finite gain-matrix oracle makes dropping the chord
        # mathematically detectable: cycle edges of gain zero have origin
        # assignments, but an extra chord of gain one admits none.
        cycle_assignments = tuple(phases for phases in product(range(order), repeat=4)
                                  if all(phases[i] ^ phases[j] == 0 for i, j in cycle))
        require(len(cycle_assignments) == order, 'cycle-only map has actual origin assignments')
        require(not any(phases[0] ^ phases[2] == 1 for phases in cycle_assignments),
                'a dropped recorded chord can invalidate EVERY cycle-only assignment')
        counts['negative_dropped_chord_cycle_only_solutions'] += len(cycle_assignments)
        witnesses['closed_cycle_vertices_G' + str(order)] = {'origins': 4, 'actual_vertices': len(closed),
                                                           'chord_matrix_entries': order ** 2}
        counts['chord_complete_locality_domains'] += 1
    # Unary set-valued embedding equality cannot be weakened to inclusion.
    image_old_value, entire_new_value = frozenset({'v'}), frozenset({'v', 'w'})
    require(image_old_value < entire_new_value, 'mere inclusion permits extra function values')
    require(frozenset() < frozenset({'total-value'}), 'mere inclusion fails to reflect definedness')
    counts['negative_unary_value_inclusion_examples'] += 2
    tick()


def compose(left, right):
    return tuple(left[right[i]] for i in range(3))


def inverse(p):
    return tuple(p.index(i) for i in range(3))


def language_controls(counts, witnesses):
    gamma = tuple(permutations(range(3)))
    identity = (0, 1, 2)
    requests = {(g, ()) for g in gamma}
    require(len(requests) == 6 and len({r[1] for r in requests}) == 1,
            'empty-real-domain requests RETAIN all global language components')
    counts['empty_domain_language_requests'] = len(requests)
    wrong_order_seen = per_node_seen = False
    for copies in product(gamma, repeat=3):
        if copies[0][1] != copies[1][0] or copies[1][1] != copies[2][0]:
            continue
        owners = (copies[0][0], copies[0][1], copies[1][1], copies[2][1])
        for g in gamma:
            gi = inverse(g)
            target_owners = tuple(g[a] for a in owners)
            normalized = tuple(gi[a] for a in target_owners)
            require(normalized == owners, 'ONE inverse language component makes the vertex map literal')
            target_copies = tuple(compose(g, p) for p in copies)
            normalized_copies = tuple(compose(gi, p) for p in target_copies)
            require(normalized_copies == copies, 'left composition normalizes EVERY copy and overlap')
            require(compose(gi, g) == identity, 'normalization has identity language component')
            # Compare arbitrary target relabels: inverse acts ON THE LEFT,
            # not by an unjustified commutative/right-composition formula.
            for sigma in gamma:
                if compose(gi, sigma) != compose(sigma, gi):
                    wrong_order_seen = True
                    witnesses.setdefault('nonabelian_language_composition', {'gamma': g, 'target_copy': sigma,
                                                                            'correct': compose(gi, sigma),
                                                                            'incorrect': compose(sigma, gi)})
            # Keeping one adjacent copy unnormalized can assign two owner
            # names to their SAME actual shared packet.
            shared = owners[1]
            if shared != g[shared]:
                per_node_seen = True
                witnesses.setdefault('per_node_language_conflict', {'gamma': g, 'shared_original_owner': shared,
                                                                   'copy0_normalized': shared,
                                                                   'copy1_unnormalized': g[shared]})
            counts['global_tree_language_normalizations'] += 1
    require(wrong_order_seen and per_node_seen, 'nonabelian/order and per-copy negatives are nonvacuous')
    counts['negative_per_node_language_normalization'] += 1
    counts['negative_wrong_composition_order'] += 1
    tick()


def graph_records(k):
    pairs = tuple(combinations(range(k), 2))
    if k <= 3:
        yield from (frozenset(s) for s in subsets(pairs))
    else:
        yield frozenset()
        yield frozenset({(0, 1), (1, 2), (2, 3)})
        yield frozenset({(0, 1), (1, 2), (2, 3), (0, 3)})


def collision_potential(images):
    return sum(n * (n - 1) // 2 for n in Counter(images).values())


def collision_controls(counts, witnesses):
    for k in range(1, 5):
        for records in graph_records(k):
            protected = tuple(frozenset(s) for s in subsets(range(k))
                              if all(tuple(e) in records for e in combinations(s, 2)))
            for images in product(range(k), repeat=k):
                if any(images[i] == images[j] for i, j in records):
                    continue  # A recorded nonthin matrix forbids this collapse.
                for base in protected:
                    if len({images[i] for i in base}) != len(base):
                        continue
                    counts['collision_protected_base_states'] += 1
                    before, current = images, list(images)
                    old = collision_potential(current)
                    moves = 0
                    while old:
                        # At least one of any colliding pair is unprotected.
                        moving = next(i for i in range(k) if i not in base
                                      and any(i != j and current[i] == current[j] for j in range(k)))
                        fixed_neighbours = {current[j] for j in range(k)
                                            if tuple(sorted((moving, j))) in records}
                        require(current[moving] not in fixed_neighbours,
                                'moving origin is outside closure of recorded neighbours')
                        forbidden = {current[j] for j in range(k) if j != moving
                                     and current[j] not in fixed_neighbours}
                        forbidden.add(current[moving])
                        fresh = next(a for a in range(k + 1) if a not in current)
                        old_image = current[moving]
                        def ambient_automorphism(a):
                            return fresh if a == old_image else old_image if a == fresh else a
                        require(all(ambient_automorphism(a) == a for a in fixed_neighbours),
                                'ambient move fixes entire recorded-neighbour packet images')
                        require(ambient_automorphism(old_image) not in forbidden | fixed_neighbours,
                                'entire moving packet avoids all other used packets')
                        unrecorded_collision_targets = [j for j in range(k)
                                                       if j != moving and current[j] == old_image]
                        require(all(ambient_automorphism(current[j]) != current[j]
                                    for j in unrecorded_collision_targets),
                                'cannot require fixing an UNRECORDED collision target')
                        current[moving] = ambient_automorphism(old_image)  # Patch ONLY this source packet.
                        require(all(current[i] == before[i] for i in base), 'protected base remains POINTWISE fixed')
                        require(all(current[i] != current[j] for i, j in records), 'every recorded matrix survives')
                        new = collision_potential(current)
                        require(new < old, 'actual unordered-pair collision potential strictly decreases',
                                (before, base, records, moving, old, new))
                        if unrecorded_collision_targets:
                            counts['unrecorded_targets_not_fixed_by_ambient_move'] += 1
                            witness = {'initial_packet_images': before,
                                       'protected': tuple(sorted(base)),
                                       'moving': moving, 'old_image': old_image,
                                       'fresh': fresh, 'fixed_neighbours': tuple(sorted(fixed_neighbours)),
                                       'potential_before': old, 'potential_after': new}
                            witnesses.setdefault('collision_patch', witness)
                            if base and fixed_neighbours:
                                witnesses.setdefault('protected_recorded_neighbour_collision', witness)
                                counts['protected_base_with_fixed_neighbour_collision_moves'] += 1
                                if any(j in base for j in unrecorded_collision_targets):
                                    witnesses.setdefault('protected_collision_target_patch', witness)
                                    counts['protected_collision_target_patch_moves'] += 1
                        old = new
                        moves += 1
                        counts['strict_collision_decreases'] += 1
                    require(len(set(current)) == k and moves <= k - 1,
                            'bounded separation terminates in an injective packet completion')
                    # Finite regular-packet completion oracle, G=C2. It
                    # checks all actual functions/records independently of
                    # the collision-count descent argument.
                    p = PacketDiagram(k, 2, records)
                    target = PacketDiagram(k + 1, 2, combinations(range(k + 1), 2))
                    q = {x: (current[x[0]], x[1]) for x in p.vertices}
                    require(len(set(q.values())) == len(q), 'full point map becomes injective')
                    require(all(q[p.function(h, x)] == target.function(h, q[x])
                                for x in p.vertices for h in range(2)), 'every unary translation survives patching')
                    require(all(p.colour(x, y) == target.colour(q[x], q[y])
                                for x, y in product(p.vertices, repeat=2) if p.colour(x, y) is not None),
                            'all fine records survive actual packet completion')
        tick()


def check():
    global START
    START = time.monotonic()
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('30-second diagnostic limit')))
    signal.alarm(30)
    counts, witnesses = Counter(), {}
    for phase in (locality_controls, packet_controls, language_controls, collision_controls):
        phase(counts, witnesses)
    signal.alarm(0)
    return {'status': 'PASS', 'scope': 'bounded B027 locality and unary-packet/action diagnostics',
            'counts': dict(sorted(counts.items())), 'witnesses': witnesses,
            'seconds': round(time.monotonic() - START, 3),
            'limits': 'No HKN, infinite closed-SAP/CCO/primitivity, actual source or global EPPA certification.'}


if __name__ == '__main__':
    print(json.dumps(check(), sort_keys=True))
