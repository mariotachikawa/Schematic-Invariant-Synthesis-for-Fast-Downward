import itertools
from typing import List, Set
import invariants
from pddl import conditions


def is_sorted_unique(lst):
    return all(lst[i] < lst[i + 1] for i in range(len(lst) - 1))


class MaxCliqueComputer:
    def __init__(self, graph: List[List[int]], max_cliques: List[List[int]]):
        self.graph = graph
        self.max_cliques = max_cliques
        self.current_max_clique = []

    def get_maximizing_vertex(self, subg: List[int], cand: List[int]) -> int:
        assert is_sorted_unique(subg), "subg is not sorted/unique"
        assert is_sorted_unique(cand), "cand is not sorted/unique"

        max_size = 0
        vertex = subg[0]

        for u in subg:
            neighbors_of_u = set(self.graph[u])
            intersection = [v for v in cand if v in neighbors_of_u]
            if len(intersection) > max_size:
                max_size = len(intersection)
                vertex = u
        return vertex

    def expand(self, subg: List[int], cand: List[int]):
        # subg: vertices, that ccan be part of maximal clique
        # cand: vertices that can be expanded for current clique
        if len(subg) == 0:
            self.max_cliques.append(self.current_max_clique[:])
        else:
            u = self.get_maximizing_vertex(subg, cand)
            neighbors_of_u = set(self.graph[u])
            ext_u = [v for v in cand if v not in neighbors_of_u]
            while ext_u: # len(ext_u) > 0:
                q = ext_u.pop()
                self.current_max_clique.append(q)
                subg_q = [v for v in subg if v in self.graph[q]] # intersetion of subg_q and neighbors of q
                cand_q = [v for v in cand if v in self.graph[q]] # intersetion of cand_q and neighbors of q
                self.expand(subg_q, cand_q)
                cand.remove(q)
                self.current_max_clique.pop()


    def compute(self):
        vertices_1 = list(range(len(self.graph)))
        vertices_2 = vertices_1[:]
        self.expand(vertices_1, vertices_2)


def compute_max_cliques(graph: List[List[int]]) -> List[List[int]]:
    max_cliques = []
    clique_computer = MaxCliqueComputer(graph, max_cliques)
    clique_computer.compute()
    return max_cliques


def generate_graph(ground_invariants: set[invariants.GroundInvariant]) -> (List[List[int]], List[conditions.Literal]):
    ground_literals = set() # make sure that every literal is only once included
    for ground_invariant in ground_invariants:
        ground_literals.update(set(ground_invariant.literals))
    ground_literals = list(ground_literals)
    literal_index_map = {literal: index for index, literal in enumerate(ground_literals)}
    graph = [[] for _ in range(len(ground_literals))]

    for ground_invariant in ground_invariants:
        if len(ground_invariant.literals) == 2:
            ground_invariant_literals = list(ground_invariant.literals)
            literal1 = ground_invariant_literals[0]
            literal2 = ground_invariant_literals[1]
            index1 = literal_index_map[literal1]
            index2 = literal_index_map[literal2]
            graph[index1].append(index2)
            graph[index2].append(index1)

    for neighbors in graph:
        neighbors.sort()

    return graph, ground_literals


def generate_mutex_groups(ground_invariants: set[invariants.GroundInvariant]) -> List[List[conditions.Atom]]:
    graph, ground_literals = generate_graph(ground_invariants)
    max_cliques = compute_max_cliques(graph)
    mutex_groups = []
    for clique in max_cliques:
        group = []
        for lit_index in clique:
            negated_literal = ground_literals[lit_index]
            assert isinstance(negated_literal, conditions.NegatedAtom)
            group.append(negated_literal.negate())
        mutex_groups.append(group)

    return mutex_groups


