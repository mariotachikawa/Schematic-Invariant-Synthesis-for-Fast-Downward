#! /usr/bin/env python3
import string
from collections import deque, defaultdict, Counter
import itertools
import random
import time
from typing import List

import invariants
import invariant_finder
import options
import pddl
import timers
import sat_check
from pddl import predicates
from pddl import conditions
from pddl import tasks
from pddl import pddl_types
from pddl import actions

TRUTH_CACHE = {}

def check_ground_literal_truth(ground_literal: conditions.Literal, atom_list: set[conditions.Atom]) -> bool:
    #print('checking groundliteral truth for: ' + str(ground_literal))
    if isinstance(ground_literal, conditions.NegatedAtom):  # true when literal not in state
        ground_literal = ground_literal.negate()
        not_in_list = ground_literal not in atom_list
        return not_in_list
    else:  # true when literal in state
        in_list = ground_literal in atom_list
        return in_list


def instantiate_atom(atom: conditions.Literal, var_mapping: dict) -> conditions.Literal:
    args = [var_mapping.get(variable) for variable in atom.args]
    inst_atom = conditions.Atom(atom.predicate, args)
    if isinstance(atom, conditions.NegatedAtom):
        inst_atom = inst_atom.negate()
    return inst_atom


def get_subtype_dict(types) -> dict[str, set[str]]:
    direct_subtypes = {}
    for t in types:
        if t.name not in direct_subtypes:
            direct_subtypes[t.name] = []
        if t.basetype_name is not None:
            if t.basetype_name not in direct_subtypes:
                direct_subtypes[t.basetype_name] = []
            direct_subtypes[t.basetype_name].append(t.name)

    subtype_dict = {}

    def find_all_subtypes(type_name):
        if type_name in subtype_dict:
            return subtype_dict[type_name]
        result = {type_name}
        for subtype in direct_subtypes.get(type_name, []):
            result |= find_all_subtypes(subtype)
        subtype_dict[type_name] = result
        return result

    for t in types:
        find_all_subtypes(t.name)

    return subtype_dict


def get_supertype_dict(types):
    supertype_dict = {t.name: set() for t in types}

    type_dict = {t.name: t for t in types}

    for t in types:
        current_type = t
        while current_type.basetype_name is not None:
            supertype_name = current_type.basetype_name
            supertype_dict[t.name].add(supertype_name)
            current_type = type_dict[supertype_name]

    return supertype_dict


def create_object_buckets(task: tasks.Task, subtype_dict) -> dict[str, set[str]]:
    object_buckets = {type_name: set() for type_name in subtype_dict}

    for obj in task.objects:
        for type_name, subtypes in subtype_dict.items():
            if obj.type_name in subtypes:
                object_buckets[type_name].add(obj.name)

    return object_buckets


def create_object_to_type_mapping(task: tasks.Task) -> dict[str, str]:
    obj_to_type = {}
    for obj in task.objects:
        obj_to_type[obj.name] = obj.type_name
    return obj_to_type


def create_predicate_buckets(task: tasks.Task, subtype_dict: dict[str, set[str]]) -> (dict, List[predicates.Predicate]):
    # key: type, value: list of predicate including an argument of type (key)
    task_types = [type_obj for type_obj in task.types if type_obj.name != type_obj.basetype_name]
    predicate_buckets = {}
    supertype_dict = get_supertype_dict(task_types)
    #subtype_dict = get_subtype_dict(task.types)

    for type_name in supertype_dict:
        predicate_buckets[type_name] = set()

    fluents = invariant_finder.get_fluents(task)
    non_fluent_names = [pred.name for pred in task.predicates if pred not in fluents]

    # add predicate to its bucket
    for p in fluents:
        for arg in p.arguments:
            predicate_buckets[arg.type_name].add(p)
            for supertype in supertype_dict[arg.type_name]:
                predicate_buckets[supertype].add(p)
            for subtype in subtype_dict[arg.type_name]:
                predicate_buckets[subtype].add(p)

    return predicate_buckets, non_fluent_names


def get_types(arguments: List[pddl_types.TypedObject]) -> List[str]:
    return [arg.type_name for arg in arguments]


def get_names(arguments: List[pddl_types.TypedObject]) -> List[str]:
    return [arg.name for arg in arguments]


def generate_var_mappings(variable_to_type_mapping: List[tuple], object_buckets: dict[str, set[str]],
                          inequalities: List[set[str]] = None):
    object_lists = []
    for var, type_name in variable_to_type_mapping:
        object_lists.append([(var, obj) for obj in object_buckets[type_name]])

    # all combinations of variable to object mappings
    for combination in itertools.product(*object_lists):
        var_mapping = dict(combination)

        # ignore inequalities
        if inequalities:
            violates_constraint = False
            for var1, var2 in inequalities:
                if var1 in var_mapping and var2 in var_mapping and var_mapping[var1] == var_mapping[var2]:
                    violates_constraint = True
                    break
            if violates_constraint:
                continue
        yield var_mapping


def create_variable_tuples(arguments: List[pddl_types.TypedObject]) -> List[tuple]:
    variable_list = []
    for argument in arguments:
        variable_list.append((argument.name, argument.type_name))

    return variable_list


def create_variable_tuples_from_candidate(variables: List[str], mapping: dict[str, str]):
    variable_list = []
    for var in variables:
        variable_list.append((var, mapping[var]))
    return variable_list


def check_schematic_literal_truth(negated_schematic_atom: conditions.NegatedAtom, variable_to_type_mapping: List[tuple],
                                  object_buckets: dict[str, set[str]], initial_atoms: set[conditions.Atom],
                                  inequalities: List[set[str]] = None) -> bool:
    is_candidate = True
    for var_mapping in generate_var_mappings(variable_to_type_mapping, object_buckets, inequalities):
        inst_literal = instantiate_atom(negated_schematic_atom, var_mapping)
        if inst_literal in TRUTH_CACHE:
            true_in_init = TRUTH_CACHE[inst_literal]
        else:
            true_in_init = check_ground_literal_truth(inst_literal, initial_atoms)
            TRUTH_CACHE[inst_literal] = true_in_init

        if true_in_init:
            continue
        else:
            is_candidate = False
            break
    return is_candidate


def check_two_schematic_literals_truth(negated_schematic_atoms: List[conditions.NegatedAtom],
                                       variable_to_type_mapping: List[tuple], object_buckets: dict[str, set[str]],
                                       initial_atoms: set[conditions.Atom],
                                       inequalities: List[set[str]] = None) -> bool:
    atom1 = negated_schematic_atoms[0]
    atom2 = negated_schematic_atoms[1]

    def check_literal(literal):
        if literal in TRUTH_CACHE:
            return TRUTH_CACHE[literal]
        truth_value = check_ground_literal_truth(literal, initial_atoms)
        TRUTH_CACHE[literal] = truth_value
        return truth_value

    checked_disjunctions = set()
    for var_mapping in generate_var_mappings(variable_to_type_mapping, object_buckets, inequalities):
        inst_literal1 = instantiate_atom(atom1, var_mapping)
        inst_literal2 = instantiate_atom(atom2, var_mapping)
        disjunction_set = frozenset([inst_literal1, inst_literal2])
        if disjunction_set not in checked_disjunctions:
            checked_disjunctions.add(disjunction_set)

            if check_literal(inst_literal1) or check_literal(inst_literal2):
                continue
            else:
                return False
    return True


def generate_negated_schematic_atom_from_predicate(predicate: predicates.Predicate) -> conditions.NegatedAtom:
    occurring_variable_names = get_names(predicate.arguments)
    negated_schematic_atom = conditions.NegatedAtom(predicate.name, occurring_variable_names)
    return negated_schematic_atom


def get_initial_schematic_invariants(task: tasks.Task, object_buckets: dict[str, set[str]], initial_atoms: set[conditions.Atom]):
    print('getting initial schematic invariants')
    initial_candidate_set = set()  # list of all invariant candidates, which are later on checked
    predicates_to_weaken = set()  # set that stores the predicates which are true in the initial state -> no weakened form
    schematic_literals = []

    #for predicate in task.predicates:
    for predicate in invariant_finder.get_fluents(task):

        negated_schematic_atom = generate_negated_schematic_atom_from_predicate(predicate)
        schematic_literals.append(negated_schematic_atom)

        variable_to_type_mapping = create_variable_tuples(predicate.arguments)
        is_candidate = check_schematic_literal_truth(negated_schematic_atom, variable_to_type_mapping, object_buckets,
                                                     initial_atoms)

        '''
        first_iteration = True
        positive_literal_true = None
        is_candidate = True
        for var_mapping in generate_var_mappings(variable_to_type_mapping, object_buckets):
            # instantiate atom for schematic_atom and negated_schematic_atom

            if first_iteration:
                inst_pos_literal = instantiate_atom(schematic_atom, var_mapping)

                if check_ground_literal_truth(inst_pos_literal, initial_atoms):
                    positive_literal_true = True

                else:
                    positive_literal_true = False
                first_iteration = False

                if not positive_literal_true:
                    inst_neg_literal = instantiate_atom(negated_schematic_atom, var_mapping)
                    if check_ground_literal_truth(inst_neg_literal, initial_atoms):
                        continue
                    else:
                        is_candidate = False
                        break
            else:
                if positive_literal_true:
                    inst_pos_literal = instantiate_atom(schematic_atom, var_mapping)
                    if check_ground_literal_truth(inst_pos_literal, initial_atoms):

                        continue
                    else:
                        is_candidate = False
                        break
                else:
                    inst_neg_literal = instantiate_atom(negated_schematic_atom, var_mapping)
                    if check_ground_literal_truth(inst_neg_literal, initial_atoms):

                        continue
                    else:
                        is_candidate = False
                        break

        if is_candidate:
            initial_predicates.add(predicate.name)
            var_mapping = {}
            for arg in predicate.arguments:
                var_mapping[arg.name] = arg.type_name
            # create schematic invariant and add it to candidates
            if positive_literal_true: # positive literal is candidate
                invariant_candidate = invariants.SchematicInvariant([schematic_atom], [], var_mapping)
            else: # negative literal is candidate
                invariant_candidate = invariants.SchematicInvariant([negated_schematic_atom], [], var_mapping)
            initial_candidate_set.add(invariant_candidate)
        '''
        if is_candidate:
            var_mapping = {}
            for arg in predicate.arguments:
                var_mapping[arg.name] = arg.type_name
            invariant_candidate = invariants.SchematicInvariant([negated_schematic_atom], [], var_mapping)
            initial_candidate_set.add(invariant_candidate)
        else:
            predicates_to_weaken.add(predicate)

    return predicates_to_weaken, initial_candidate_set, schematic_literals


def sort_types(types: List[pddl_types.Type], subtype_dict: dict[str, set[str]]) -> List[str]:
    types_sorted = sorted(types, key=lambda t: len(subtype_dict[t.name]))

    return [t.name for t in types_sorted]


def calculate_l_numbers(task: tasks.Task) -> dict[str, int]:
    l_action = {}  # key: type, value: l_number
    l_predicate = {}  # key: type, value: l_number
    l_numbers = {}  # key: type, value: l_number
    task_types = [type_obj for type_obj in task.types if type_obj.name != type_obj.basetype_name]
    for task_type in task_types:
        l_action[task_type.name] = 0
        l_predicate[task_type.name] = 0
        l_numbers[task_type.name] = 0
    for action in task.actions:
        type_names = [typed_object.type_name for typed_object in action.parameters]
        type_counts = Counter(type_names)

        for t, count in type_counts.items():
            if count > l_action[t]:
                l_action[t] = count

    for predicate in task.predicates:
    #for predicate in invariant_finder.get_fluents(task):
        type_names = [typed_object.type_name for typed_object in predicate.arguments]
        type_counts = Counter(type_names)

        for t, count in type_counts.items():
            if count > l_predicate[t]:
                l_predicate[t] = count

    for task_type in task_types:
        current_type = task_type.name
        if l_predicate[current_type] > l_action[current_type]:
            l_numbers[current_type] = 2 * l_predicate[current_type]
        else:
            l_numbers[current_type] = l_predicate[current_type] + l_action[current_type]
    return l_numbers


def generate_limited_grounding_function(task: tasks.Task, object_buckets: dict[str, set[str]],
                                        subtype_dict: dict[str, set[str]]) -> dict[str, set[str]]:
    limited_object_buckets = {}
    task_types = [type_obj for type_obj in task.types if type_obj.name != type_obj.basetype_name]
    for task_type in task_types:
        limited_object_buckets[task_type.name] = set()

    # calculate all L values
    l_numbers = calculate_l_numbers(task)  # mapping from type name to integer
    sorted_types = sort_types(task_types, subtype_dict)
    for t in sorted_types:
        if l_numbers[t] >= len(object_buckets[t]):
            limited_object_buckets[t].update(object_buckets[t])
            continue
        for subtype in subtype_dict[t]:
            if subtype != t:
                limited_object_buckets[t].update(limited_object_buckets[subtype])
        obj_count = len(limited_object_buckets[t])
        while obj_count < l_numbers[t]:
            for object_name in object_buckets[t]:
                if object_name not in limited_object_buckets[t]:
                    limited_object_buckets[t].add(object_name)
                    obj_count += 1
                    break
    return limited_object_buckets


def generate_groundings(schematic_invariant: invariants.SchematicInvariant,
                        object_buckets: dict[str, set[str]]) -> set[invariants.GroundInvariant]:
    groundings = set()
    schematic_literals = schematic_invariant.literals
    inequalities = schematic_invariant.inequalities
    mapping = schematic_invariant.var_mapping

    variables = [var for literal in schematic_literals for var in literal.args]
    var_to_type_tuples = create_variable_tuples_from_candidate(variables, mapping)

    for var_mapping in generate_var_mappings(var_to_type_tuples, object_buckets, inequalities):
        ground_literals = set()
        for literal in schematic_literals:
            ground_literal = instantiate_atom(literal, var_mapping)
            assert isinstance(ground_literal, conditions.NegatedAtom)
            ground_literals.add(ground_literal)
        ground_invariant = invariants.GroundInvariant(ground_literals)
        groundings.add(ground_invariant)

    return groundings


def generate_instantiated_actions(task: tasks.Task, object_buckets: dict[str, set[str]], initial_atoms: set[conditions.Atom], non_fluents: List[str]):
    instantiated_actions = set()
    for action in task.actions:
        name = action.name
        typed_objects = action.parameters
        precondition_atoms = list(action.precondition.parts)
        effects = action.effects
        effect_literals = [effect.literal for effect in effects]
        var_to_type_tuples = create_variable_tuples(typed_objects)
        for var_mapping in generate_var_mappings(var_to_type_tuples, object_buckets):
            objects = [var_mapping.get(typed_object.name) for typed_object in typed_objects]
            inst_preconditions = [instantiate_atom(prec_atom, var_mapping) for prec_atom in precondition_atoms]

            # remove action if precondition contains non_fluent predicate that is not contained in init state
            '''
            reachable_action = True
            for prec_atom in inst_preconditions:
                if prec_atom.predicate in non_fluents:
                    if prec_atom not in initial_atoms:
                        reachable_action = False
                        break
            if not reachable_action:
                continue
            '''

            inst_effects = [instantiate_atom(effect_literal, var_mapping) for effect_literal in effect_literals]
            inst_action = actions.InstantiatedAction(name, objects, inst_preconditions, inst_effects)
            instantiated_actions.add(inst_action)
    return instantiated_actions


def generate_regression(action: actions.InstantiatedAction, candidate: invariants.GroundInvariant) -> List[conditions.Literal]:
    regression = []
    regression.extend(action.precondition)
    negated_literals = [literal.negate() for literal in candidate.literals]
    for effect_literal in action.effects:
        assert isinstance(effect_literal, (conditions.Atom, conditions.NegatedAtom))
        if effect_literal in negated_literals:
            negated_literals.remove(effect_literal)

        neg_effect_literal = effect_literal.negate()
        if neg_effect_literal in negated_literals:
            negated_literals.append(effect_literal) #makes sure that if action deletes negated literal in candidate, sat check returns false
    regression.extend(negated_literals)

    return regression


def generate_all_groundings(task, object_buckets: dict[str, set[str]], groundings_c: set[invariants.GroundInvariant], candidates_to_weaken: set[invariants.GroundInvariant]):
    grounding_set = set()
    #for predicate in task.predicates:
    for predicate in invariant_finder.get_fluents(task):
        negated_schematic_atom = generate_negated_schematic_atom_from_predicate(predicate)
        variable_to_type_mapping = create_variable_tuples(predicate.arguments)
        for var_mapping in generate_var_mappings(variable_to_type_mapping, object_buckets):
            inst_literal = instantiate_atom(negated_schematic_atom, var_mapping)
            assert isinstance(inst_literal, conditions.NegatedAtom)
            can_be_added = True

            difference_groundings = groundings_c - candidates_to_weaken
            for ground_candidate in difference_groundings:
                if len(ground_candidate.literals) == 1:
                    ground_candidate_literals = list(ground_candidate.literals)
                    ground_candidate_literal = ground_candidate_literals[0]
                    if inst_literal == ground_candidate_literal:
                        can_be_added = False
                        break
            
            if can_be_added:
                grounding_set.add(inst_literal)

    return grounding_set


def update_candidate_set(task, groundings_c: set[invariants.GroundInvariant],
                         candidates_to_weaken: set[invariants.GroundInvariant],
                         object_buckets: dict[str, set[str]]) -> set[invariants.GroundInvariant]:
    for candidate_to_weaken in candidates_to_weaken:
        candidate_to_weaken_literals = list(candidate_to_weaken.literals)
        if len(candidate_to_weaken_literals) == 1:
            all_groundings = generate_all_groundings(task, object_buckets, groundings_c, candidates_to_weaken)
            candidate_to_weaken_literal = candidate_to_weaken_literals[0]
            for literal_to_add in all_groundings:
                if candidate_to_weaken_literal != literal_to_add:
                    ground_literals = set()
                    ground_literals.add(literal_to_add)
                    ground_literals.update(candidate_to_weaken.literals)
                    new_candidate = invariants.GroundInvariant(ground_literals)
                    groundings_c.add(new_candidate)
        groundings_c.remove(candidate_to_weaken)

    return groundings_c


def run_rintanen(task,
                 initial_candidate_set: set[invariants.SchematicInvariant],
                 object_buckets: dict[str, set[str]], non_fluents: List[str], initial_atoms: set[conditions.Atom]):
    print('running rintanens algorithm')
    # create all instantiated actions
    inst_actions = generate_instantiated_actions(task, object_buckets, initial_atoms, non_fluents)

    # create all groundings
    groundings_c = set()
    for candidate in initial_candidate_set:
        new_groundings = generate_groundings(candidate, object_buckets)
        groundings_c.update(new_groundings)

    while True:
        groundings_c0 = groundings_c.copy()
        candidates_to_weaken = set()
        #print(len(groundings_c))
        for c in groundings_c:
            #test
            c_lit = list(c.literals)
            if len(c_lit) == 2:
                lit1 = c_lit[0]
                lit2 = c_lit[1]
            #test end
            for a in inst_actions:
                regression = generate_regression(a, c)

                if sat_check.check_sat_rintanen_invariant_synthesis(groundings_c0, regression):
                    #print(c)
                    candidates_to_weaken.add(c)
                    break
        #if groundings_c0 == groundings_c:  # it would also be possible to check if candidates_to_weaken is empty -> more efficient?
           # break
        if len(candidates_to_weaken) == 0:
            break
        else:
            groundings_c = update_candidate_set(task, groundings_c, candidates_to_weaken, object_buckets)

    invariant_set = ground_to_schematic(task, groundings_c)
    #print('found ground invariants:')
    #for ground_inv in groundings_c:
     #   print(ground_inv)

    print('found schematic invariants:')
    for schematic_inv in invariant_set:
        print(schematic_inv)

    return invariant_set


def ground_to_schematic(task: tasks.Task, ground_invariants: set[invariants.GroundInvariant]):
    schematic_invariants = set()
    obj_to_type = create_object_to_type_mapping(task)
    variable_names = list(string.ascii_lowercase[:26])  # alphabet

    for ground_invariant in ground_invariants:
        var_mapping = {}
        inequalities = []
        current_variable_name_index = 0
        literals = list(ground_invariant.literals)
        processed_indx = set()
        objects = [obj for literal in literals for obj in literal.args]
        variables = objects.copy()
        # find equalities
        for i in range(len(objects)):
            if i in processed_indx:
                continue
            processed_indx.add(i)
            variables[i] = variable_names[current_variable_name_index]
            current_variable_name_index += 1
            var_mapping[variables[i]] = obj_to_type[objects[i]]
            for j in range(i + 1, len(objects)):
                if j in processed_indx:
                    continue

                if objects[i] == objects[j]:
                    variables[j] = variables[i]
                    processed_indx.add(j)

        for i in range(len(variables) - 1):
            for j in range(i + 1, len(variables)):
                if variables[i] != variables[j]:
                    inequalities.append({variables[i], variables[j]})

        schematic_literals = []
        for literal in literals:
            args = variables[:len(literal.args)]
            variables = variables[len(literal.args):]
            schematic_literal = conditions.NegatedAtom(literal.predicate, args)
            schematic_literals.append(schematic_literal)
        schematic_invariant = invariants.SchematicInvariant(schematic_literals, inequalities, var_mapping)
        schematic_invariants.add(schematic_invariant)
    return schematic_invariants


def schematic_to_ground(object_buckets: dict[str, set[str]],
                        schematic_invariant_set: set[invariants.SchematicInvariant]) -> set[invariants.GroundInvariant]:
    ground_invariants = set()
    for schematic_invariant in schematic_invariant_set:
        new_groundings = generate_groundings(schematic_invariant, object_buckets)
        ground_invariants.update(new_groundings)

    return ground_invariants


def set_variables_equal(predicate: predicates.Predicate,
                        subtype_dict: dict[str, set[str]],
                        object_buckets: dict[str, set[str]],
                        initial_atoms: set[conditions.Atom]):
    #print('setting vars equal')
    occurring_names = get_names(predicate.arguments)

    candidates = []
    non_candidates = []
    for i in range(len(predicate.arguments) - 1):
        for j in range(i + 1, len(predicate.arguments)):
            if not predicate.arguments[i].name == predicate.arguments[j].name:
                if predicate.arguments[i].type_name in subtype_dict[predicate.arguments[j].type_name] or \
                        predicate.arguments[j].type_name in subtype_dict[predicate.arguments[i].type_name]:

                    if predicate.arguments[i].type_name in subtype_dict[predicate.arguments[j].type_name]:
                        shared_type = predicate.arguments[i].type_name
                    else:
                        shared_type = predicate.arguments[j].type_name

                    variable_names = occurring_names
                    variable_name_to_remove = variable_names[j]
                    variable_names[j] = variable_names[i]
                    variable_to_type_mapping = [mapping for mapping in create_variable_tuples(predicate.arguments)
                                                if mapping[0] != variable_name_to_remove]
                    for idx in range(len(variable_to_type_mapping)):
                        var, type_name = variable_to_type_mapping[idx]
                        if var == variable_names[i]:
                            variable_to_type_mapping[idx] = (var, shared_type)

                    schematic_literal = conditions.NegatedAtom(predicate.name, variable_names)
                    is_candidate = check_schematic_literal_truth(schematic_literal,
                                                                 variable_to_type_mapping,
                                                                 object_buckets,
                                                                 initial_atoms)

                    var_mapping = {}
                    for var, type_name in variable_to_type_mapping:
                        var_mapping[var] = type_name
                    schematic_candidate = invariants.SchematicInvariant([schematic_literal], [], var_mapping)
                    if is_candidate:
                        if schematic_candidate not in candidates:
                            candidates.append(schematic_candidate)
                    else:
                        if schematic_candidate not in non_candidates:
                            non_candidates.append(schematic_candidate)

    return candidates, non_candidates


def set_variables_unequal(predicate: predicates.Predicate,
                          subtype_dict: dict[str, set[str]],
                          object_buckets: dict[str, set[str]],
                          initial_atoms: set[conditions.Atom]):
    #print('setting vars not equal')
    occurring_names = get_names(predicate.arguments)
    candidates = []
    non_candidates = []

    for i in range(len(predicate.arguments) - 1):
        for j in range(i + 1, len(predicate.arguments)):
            if not predicate.arguments[i].name == predicate.arguments[j].name:
                if predicate.arguments[i].type_name in subtype_dict[predicate.arguments[j].type_name] or \
                        predicate.arguments[j].type_name in subtype_dict[predicate.arguments[i].type_name]:

                    variable_to_type_mapping = create_variable_tuples(predicate.arguments)
                    schematic_literal = conditions.NegatedAtom(predicate.name, occurring_names)
                    inequality_set = {predicate.arguments[i].name, predicate.arguments[j].name}

                    # test reason
                    '''
                    var_mapping = {}
                    for var, type_name in variable_to_type_mapping:
                        var_mapping[var] = type_name
                    schematic_candidate = invariants.SchematicInvariant([schematic_literal], [inequality_set],
                                                                        var_mapping)
                    print(schematic_candidate)
                    '''
                    # test reason end

                    is_candidate = check_schematic_literal_truth(schematic_literal, variable_to_type_mapping,
                                                                 object_buckets, initial_atoms, [inequality_set])
                    var_mapping = {}
                    for var, type_name in variable_to_type_mapping:
                        var_mapping[var] = type_name
                    schematic_candidate = invariants.SchematicInvariant([schematic_literal], [inequality_set],
                                                                        var_mapping)
                    if is_candidate:
                        if schematic_candidate not in candidates:
                            candidates.append(schematic_candidate)
                    else:
                        if schematic_candidate not in non_candidates:
                            non_candidates.append(schematic_candidate)

    return candidates, non_candidates


def add_literal(predicate: predicates.Predicate,
                predicates_to_add: List[predicates.Predicate],
                predicate_buckets: dict[str, set[predicates.Predicate]]):
    #print('adding literal')
    #candidates = set()
    non_candidates = set()

    possible_predicates = {p for arg in predicate.arguments for p in predicate_buckets[arg.type_name]}
    possible_predicates &= set(predicates_to_add)

    for other_predicate in possible_predicates:
        combined_arg_list = predicate.arguments + [pddl_types.TypedObject('other' + arg.name, arg.type_name)
                                                   for arg in other_predicate.arguments]
        this_variable_names = get_names(predicate.arguments)
        other_variable_names = get_names(combined_arg_list[len(predicate.arguments):])
        variable_to_type_mapping = create_variable_tuples(combined_arg_list)

        this_schematic_literal = conditions.NegatedAtom(predicate.name, this_variable_names)
        other_schematic_literal = conditions.NegatedAtom(other_predicate.name, other_variable_names)
        schematic_list = [this_schematic_literal, other_schematic_literal]

        #is_candidate = check_two_schematic_literals_truth(schematic_list, variable_to_type_mapping, object_buckets, initial_atoms)
        schematic_candidate = invariants.SchematicInvariant(schematic_list, [], dict(variable_to_type_mapping))

        #not necessary to check if the disjunction is true in the initial state, because we already know they are not
        #if is_candidate:
            #candidates.add(schematic_candidate)
        #else:
            #non_candidates.add(schematic_candidate)
        non_candidates.add(schematic_candidate)

    return list(non_candidates)


def set_candidate_eq(candidate: invariants.SchematicInvariant,
                     subtype_dict: dict[str, set[str]],
                     object_buckets: dict[str, set[str]],
                     initial_atoms: set[conditions.Atom]):
    literals = candidate.literals
    inequalities = candidate.inequalities
    mapping = candidate.var_mapping
    candidates = []
    non_candidates = []

    if len(literals) == 1:  # single literal
        literal = literals[0]
        predicate = literal.predicate
        variables = list(literal.args)
        for i in range(len(variables) - 1):
            for j in range(i + 1, len(variables)):
                if not (variables[i] == variables[j]):
                    comparison_set = {variables[i], variables[j]}
                    if not (comparison_set in inequalities):
                        if mapping[variables[i]] in subtype_dict[mapping[variables[j]]] or \
                                mapping[variables[j]] in subtype_dict[mapping[variables[i]]]:

                            if mapping[variables[i]] in subtype_dict[mapping[variables[j]]]:
                                shared_type = mapping[variables[i]]
                            else:
                                shared_type = mapping[variables[j]]
                            variables_for_literal = variables.copy()
                            variables_for_literal[j] = variables_for_literal[i]
                            variables_for_mapping = variables.copy()
                            variables_for_mapping.remove(variables_for_mapping[j])
                            variable_to_type_mapping = create_variable_tuples_from_candidate(variables, mapping)
                            for idx in range(len(variable_to_type_mapping)):
                                var, type_name = variable_to_type_mapping[idx]
                                if var == variables[i]:
                                    variable_to_type_mapping[idx] = (var, shared_type)

                            schematic_literal = conditions.NegatedAtom(predicate, variables_for_literal)
                            is_candidate = check_schematic_literal_truth(schematic_literal, variable_to_type_mapping,
                                                                         object_buckets, initial_atoms, inequalities)
                            var_mapping = {}
                            for var, type_name in variable_to_type_mapping:
                                var_mapping[var] = type_name
                            schematic_candidate = \
                                invariants.SchematicInvariant([schematic_literal], inequalities, var_mapping)
                            if is_candidate:
                                if schematic_candidate not in candidates:
                                    candidates.append(schematic_candidate)
                            else:
                                if schematic_candidate not in non_candidates:
                                    non_candidates.append(schematic_candidate)


    else:  # disjunction
        literal1 = literals[0]
        literal2 = literals[1]
        predicate1 = literal1.predicate
        predicate2 = literal2.predicate
        variables1 = list(literal1.args)
        variables2 = list(literal2.args)
        var1_size = len(variables1)
        variables = variables1 + variables2
        for i in range(len(variables) - 1):
            for j in range(i + 1, len(variables)):
                if not (variables[i] == variables[j]):
                    comparison_set = {variables[i], variables[j]}
                    if not (comparison_set in inequalities):
                        if mapping[variables[i]] in subtype_dict[mapping[variables[j]]] or \
                                mapping[variables[j]] in subtype_dict[mapping[variables[i]]]:

                            if mapping[variables[i]] in subtype_dict[mapping[variables[j]]]:
                                shared_type = mapping[variables[i]]
                            else:
                                shared_type = mapping[variables[j]]
                            variables_for_literal = variables.copy()
                            variables_for_literal[j] = variables_for_literal[i]
                            variables_for_mapping = variables.copy()
                            variables_for_mapping.remove(variables_for_mapping[j])
                            variable_to_type_mapping = \
                                create_variable_tuples_from_candidate(variables_for_mapping, mapping)
                            for idx in range(len(variable_to_type_mapping)):
                                var, type_name = variable_to_type_mapping[idx]
                                if var == variables[i]:
                                    variable_to_type_mapping[idx] = (var, shared_type)

                            schematic_literal1 = conditions.NegatedAtom(predicate1, variables_for_literal[:var1_size])
                            schematic_literal2 = conditions.NegatedAtom(predicate2, variables_for_literal[var1_size:])
                            is_candidate = check_two_schematic_literals_truth([schematic_literal1, schematic_literal2],
                                                                              variable_to_type_mapping,
                                                                              object_buckets,
                                                                              initial_atoms,
                                                                              inequalities)
                            var_mapping = {}
                            for var, type_name in variable_to_type_mapping:
                                var_mapping[var] = type_name
                            schematic_candidate = \
                                invariants.SchematicInvariant([schematic_literal1, schematic_literal2],
                                                              inequalities,
                                                              var_mapping)
                            if is_candidate:
                                if schematic_candidate not in candidates:
                                    candidates.append(schematic_candidate)
                            else:
                                if schematic_candidate not in non_candidates:
                                    non_candidates.append(schematic_candidate)

    return candidates, non_candidates


def set_candidate_unequal(candidate: invariants.SchematicInvariant,
                          subtype_dict: dict[str, set[str]],
                          object_buckets: dict[str, set[str]],
                          initial_atoms: set[conditions.Atom]):
    literals = candidate.literals
    mapping = candidate.var_mapping
    candidates = []
    non_candidates = []

    if len(literals) == 1:
        literal = literals[0]
        predicate = literal.predicate
        variables = list(literal.args)
        for i in range(len(variables) - 1):
            for j in range(i + 1, len(variables)):
                inequalities = candidate.inequalities.copy()
                if not (variables[i] == variables[j]):
                    comparison_set = {variables[i], variables[j]}
                    if not (comparison_set in inequalities):
                        if mapping[variables[i]] in subtype_dict[mapping[variables[j]]] or mapping[variables[j]] in \
                                subtype_dict[mapping[variables[i]]]:
                            new_inequality = {variables[i], variables[j]}
                            inequalities.append(new_inequality)
                            variable_to_type_mapping = create_variable_tuples_from_candidate(variables, mapping)
                            schematic_literal = conditions.NegatedAtom(predicate, variables)
                            is_candidate = check_schematic_literal_truth(schematic_literal, variable_to_type_mapping,
                                                                         object_buckets, initial_atoms, inequalities)
                            var_mapping = {}
                            for var, type_name in variable_to_type_mapping:
                                var_mapping[var] = type_name
                            schematic_candidate = invariants.SchematicInvariant([schematic_literal], inequalities,
                                                                                var_mapping)
                            if is_candidate:
                                if schematic_candidate not in candidates:
                                    candidates.append(schematic_candidate)
                            else:
                                if schematic_candidate not in non_candidates:
                                    non_candidates.append(schematic_candidate)


    else:  # disjunction
        literal1 = literals[0]
        literal2 = literals[1]
        predicate1 = literal1.predicate
        predicate2 = literal2.predicate
        variables1 = list(literal1.args)
        variables2 = list(literal2.args)
        var1_size = len(variables1)
        variables = variables1 + variables2
        for i in range(len(variables) - 1):
            for j in range(i + 1, len(variables)):
                inequalities = candidate.inequalities.copy()
                if not (variables[i] == variables[j]):
                    comparison_set = {variables[i], variables[j]}
                    if not (comparison_set in inequalities):
                        if mapping[variables[i]] in subtype_dict[mapping[variables[j]]] or mapping[variables[j]] in \
                                subtype_dict[mapping[variables[i]]]:
                            new_inequality = {variables[i], variables[j]}
                            inequalities.append(new_inequality)
                            variable_to_type_mapping = create_variable_tuples_from_candidate(variables, mapping)

                            schematic_literal1 = conditions.NegatedAtom(predicate1, variables[:var1_size])
                            schematic_literal2 = conditions.NegatedAtom(predicate2, variables[var1_size:])
                            is_candidate = check_two_schematic_literals_truth([schematic_literal1, schematic_literal2],
                                                                              variable_to_type_mapping,
                                                                              object_buckets, initial_atoms,
                                                                              inequalities)
                            var_mapping = {}
                            for var, type_name in variable_to_type_mapping:
                                var_mapping[var] = type_name
                            schematic_candidate = invariants.SchematicInvariant(
                                [schematic_literal1, schematic_literal2], inequalities, var_mapping)
                            if is_candidate:
                                if schematic_candidate not in candidates:
                                    candidates.append(schematic_candidate)
                            else:
                                if schematic_candidate not in non_candidates:
                                    non_candidates.append(schematic_candidate)

    return candidates, non_candidates


def add_additional_candidates(predicates_to_weaken: set, initial_schematic_candidates_set: set,
                              object_buckets: dict[str, set[str]], subtype_dict: dict[str, set[str]],
                              initial_atoms: set[conditions.Atom], predicate_buckets: dict) \
                                -> set[invariants.SchematicInvariant]:
    candidates_to_weaken = set()
    print('adding additional candidates')
    #print('predicates to weaken:')
    #for predic in predicates_to_weaken:
        #print(predic.name)

    remaining_predicates = list(predicates_to_weaken)
    for predicate in predicates_to_weaken:
        #print('current predicate:')
        #print(predicate.name)
        eq_candidates, non_eq_candidates = set_variables_equal(predicate, subtype_dict, object_buckets, initial_atoms)
        neq_candidates, non_neq_candidates = set_variables_unequal(predicate, subtype_dict, object_buckets,
                                                                   initial_atoms)
        non_disj_candidates = add_literal(predicate, remaining_predicates, predicate_buckets)

        candidates_to_weaken.update(non_eq_candidates)
        candidates_to_weaken.update(non_neq_candidates)
        candidates_to_weaken.update(non_disj_candidates)

        new_schematic_candidates = eq_candidates + neq_candidates #+ disj_candidates
        if len(new_schematic_candidates) > 0:
            initial_schematic_candidates_set.update(new_schematic_candidates)

        remaining_predicates.remove(predicate)

    while candidates_to_weaken:
        candidate = candidates_to_weaken.pop()

        #print(len(candidates_to_weaken))
        #print(candidate)
        eq_candidates, non_eq_candidates = set_candidate_eq(candidate, subtype_dict, object_buckets, initial_atoms)
        neq_candidates, non_neq_candidates = set_candidate_unequal(candidate, subtype_dict, object_buckets,
                                                                   initial_atoms)

        candidates_to_weaken.update(non_eq_candidates)
        candidates_to_weaken.update(non_neq_candidates)
        new_schematic_candidates = eq_candidates + neq_candidates
        if len(new_schematic_candidates) > 0:
            initial_schematic_candidates_set.update(new_schematic_candidates)

        remove_unnecessary_weak_forms(initial_schematic_candidates_set, candidates_to_weaken)

    return initial_schematic_candidates_set


def remove_unnecessary_weak_forms(schematic_candidates: set[invariants.SchematicInvariant],
                                  candidates_to_weaken: set[invariants.SchematicInvariant]):
    single_literal_candidates = []
    disj_candidates = []
    for candidate in schematic_candidates:
        if len(candidate.literals) == 1:
            single_literal_candidates.append(candidate)
    for candidate_to_weaken in candidates_to_weaken:
        if len(candidate_to_weaken.literals) == 2:
            disj_candidates.append(candidate_to_weaken)

    candidates_to_remove = set()
    for single_candidate in single_literal_candidates:
        single_literal = single_candidate.literals[0]
        assert isinstance(single_literal, conditions.NegatedAtom)
        vars = list(single_literal.args)
        equalities = []
        inequalities = []
        for i in range(len(vars) - 1):
            for j in range(i + 1, len(vars)):
                if vars[i] == vars[j]:
                    equalities.append((i, j))
                elif {vars[i], vars[j]} in single_candidate.inequalities:
                    inequalities.append((i, j))
        for disj_candidate in disj_candidates:
            to_remove = True
            for disj_literal in disj_candidate.literals:
                disj_vars = disj_literal.args
                if disj_literal.predicate == single_literal.predicate:
                    for eq in equalities:
                        if not disj_vars[eq[0]] == disj_vars[eq[1]]:
                            to_remove = False
                            break
                    if to_remove:
                        for ineq in inequalities:
                            if not {disj_vars[ineq[0]], disj_vars[ineq[1]]} in disj_candidate.inequalities:
                                to_remove = False
                                break
                    if to_remove:
                        candidates_to_remove.add(disj_candidate)
                        break
    candidates_to_weaken.difference_update(candidates_to_remove)


def find_schematic_invariants(task):
    task_types = [type_obj for type_obj in task.types if type_obj.name != type_obj.basetype_name]
    subtype_dict = get_subtype_dict(task_types)
    object_buckets = create_object_buckets(task, subtype_dict)
    limited_object_buckets = generate_limited_grounding_function(task, object_buckets, subtype_dict)
    predicate_buckets, non_fluents = create_predicate_buckets(task, subtype_dict)
    initial_atoms = [atom for atom in task.init if isinstance(atom, conditions.Atom)]
    initial_atoms = set(initial_atoms)
    predicates_to_weaken, initial_candidate_set, schematic_literals =\
        get_initial_schematic_invariants(task, object_buckets, initial_atoms)
    initial_schematic_candidates_set = add_additional_candidates(predicates_to_weaken, initial_candidate_set,
                                                                 object_buckets, subtype_dict, initial_atoms,
                                                                 predicate_buckets)
    #for item in initial_schematic_candidates_set:
     #   print(item)
    schematic_invariants = run_rintanen(task, initial_schematic_candidates_set, limited_object_buckets, non_fluents, initial_atoms)
    ground_invariants = schematic_to_ground(object_buckets, schematic_invariants)

    return ground_invariants
