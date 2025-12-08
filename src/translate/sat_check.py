from typing import List

from pddl import conditions

import invariants


def check_sat_rintanen_invariant_synthesis(candidates: set[invariants.GroundInvariant],
                                           regression: List[conditions.Literal]):
    """
        candidates: List[List[Literal]],
        regression: List[Literal]):
        Checks if the conjunction of candidate invariants and the regression
       of a negated candidate as in the invariant synthesis algorithm
       in Rintanen 2017 is satisfiable.

       This implementation assumes that
       - each candidate is a disjunction of at most two literals,
       - the set of candidates is satisfiable, and
       - the set of candidates is closed under resolution.

       The initial set of candidates satisfies these assumptions by construction.
       During the algorithm, if a resolvent of two clauses is removed in the inner loop,
       at least one of its antecedents is also removed, and C_0 is only updated after
       checking all candidates once, thus C_0 satisfies the assumptions at any time
       (while C might not).
    """
    # The regression itself could be unsatisfiable. -> not necessary, because only negative literals

    for lit in regression:
        assert isinstance(lit, (conditions.Atom, conditions.NegatedAtom))
        neg_lit = lit.negate()
        if neg_lit in regression:
            return False

    # As the set of candidates is satisfiable and closed under resolution,
    # the only way that the whole conjunction can be unsatisfiable is that
    # the literals of the regression falsify a candidate.
    for candidate in candidates:
        cand_literals = list(candidate.literals)
        assert len(cand_literals) == 1 or len(cand_literals) == 2

        first_lit = cand_literals[0]
        assert isinstance(first_lit, (conditions.Atom, conditions.NegatedAtom))
        if first_lit.negate() in regression:
            if len(cand_literals) == 1:
                return False
            second_lit = cand_literals[1]
            assert isinstance(second_lit, (conditions.Atom, conditions.NegatedAtom))
            if second_lit.negate() in regression:
                return False

    return True
