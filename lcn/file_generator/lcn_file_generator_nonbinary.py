from itertools import product
import math
from lcn.file_generator.logger import Logger
from lcn.file_generator.graph import Graph
from lcn.file_generator.c_component import CComponent

def bound_canonical_partitions(dag_components: list[list[int]], cardinalities: list[int], parents: list[int]):
    partitions: list[int] = []
    for i, component in enumerate(dag_components):
        canonical_partition = 1
        for node in component.nodes:
            if cardinalities[node] > 1:
                base = cardinalities[node]
                exponent = 1
                for parent in parents[node]:
                    if cardinalities[parent] > 1:
                        exponent *= cardinalities[parent]
                canonical_partition *= math.pow(base, exponent)
        print(f"For the c-component #{i + 1} the equivalent canonical partition = {int(canonical_partition)}")    
        partitions.append(canonical_partition)
    
    return partitions

def calculate_ccomponents(variables, edges, verbose=False):
    graph = Graph.parse_for_lcn(variables, edges)    
        
    CComponent.find_cComponents(graph)
    
    if verbose:
        Logger.debugGraph(graph)
        Logger.debugCcomponents(graph)

    latentCardinalities: list[int] = bound_canonical_partitions(graph.dag_components, graph.cardinalities, graph.parents)

    latentCardinalities = [int(x) for x in latentCardinalities]

    for i, component in enumerate(graph.dag_components):
        for node in component.nodes:
            if graph.cardinalities[node] < 1: # Exogenous variable
                variables[graph.index_to_label[node]] = latentCardinalities[i]

def parse_input(edges_str, unob_str, cardinalities):
    edges = edges_str.split(", ")
    unob = unob_str.split(", ") if unob_str else []

    dag = {}
    variables = {}

    for edge in edges:
        parent, child = edge.split(" -> ")

        if parent not in variables:
            if parent in unob:
                variables[parent] = 0
            elif parent in cardinalities:
                variables[parent] = cardinalities[parent]
            else:
                variables[parent] = 2
        if child not in variables:
            if child in cardinalities:
                variables[child] = cardinalities[child]
            else:
                variables[child] = 2

        if child in dag:
            dag[child].append(parent)
        else:
            dag[child] = [parent]

        if parent not in dag:
            dag[parent] = []

    print("Parsed DAG:", dag)
    return dag, unob, variables, edges

# Identify endogenous variables without exogenous parents and create auxiliary exogenous variables (for twin network purposes)
def create_auxiliary_exogenous(dag, unob, variables):
    auxiliary_exo_vars = []
    for child, parents in dag.items():
        if (child not in unob) and (not any(p in unob for p in parents)):
            aux_exo = f"Uaux_{child}"
            unob.append(aux_exo)
            auxiliary_exo_vars.append(aux_exo)
            dag[child].append(aux_exo)
            variables[aux_exo] = variables[child]**(math.prod(variables[p] for p in parents if p not in unob))

def generate_mechanism(var, parents, unob, variables, twin=False, verbose=False):

    def convert_base(n, b, significant_places=0):
        if n == 0:
            digits = [0]
        else:
            digits = []
            while n:
                digits.append(n % b)
                n //= b
            digits = digits[::-1]

        if significant_places > len(digits): # Pad with leading zeros if necessary
            digits = [0] * (significant_places - len(digits)) + digits
        elif significant_places < len(digits): # Truncate the most significant digits if there are too many
            digits = digits[-significant_places:]
        
        return digits
    
    rhs_list = []
    lhs_list = []
    sentences = []

    exo_parents = [p for p in parents if p in unob]
    endo_parents = [p for p in parents if p not in unob]
    ordered_parents = exo_parents + endo_parents
    num_exo_parents_combinations = math.prod(variables[p] for p in exo_parents)
    num_endo_parents_combinations = math.prod(variables[p] for p in endo_parents)
    ranges = [range(variables[p]) for p in ordered_parents]
    worlds = list(product(*ranges))
    
    for world in worlds:
        parent_values = [f"({ordered_parents[i]}{'L' if twin and ordered_parents[i] in endo_parents else ''} = {world[i]})" for i in range(len(world))]
        rhs = " and ".join(parent_values)
        rhs_list.append(rhs)

    for i in range(num_exo_parents_combinations):
        evaluations = convert_base(i, variables[var], num_endo_parents_combinations)
        for digit in evaluations:
            lhs = f"{var} = {digit}" if twin == False else f"{var}L = {digit}"
            lhs_list.append(lhs)

    if verbose:
        print(f"number of worlds for var {var}: {len(worlds)}")
        for p in parents:
            print((f"exo" if p in exo_parents else f"endo") + f"parent {p} cardinality: {variables[p]}")
        print(f"num_exo_parents_combinations: {num_exo_parents_combinations}, num_endo_parents_combinations: {num_endo_parents_combinations}")
        print(f"len(rhs_list): {len(rhs_list)}, len(lhs_list): {len(lhs_list)}")
        print(f"  lhs   |              rhs              ")
        for i in range(min(len(lhs_list), len(rhs_list), 10)):
            print(f"{lhs_list[i]}  |  {rhs_list[i]}")
        print("")

    if len(lhs_list) != len(rhs_list):
        raise ValueError("Number of lhs and rhs sentences do not match")
    
    for lhs, rhs in zip(lhs_list, rhs_list):
        sentence = f"1 <= P({lhs} | {rhs}) <= 1"
        sentences.append(sentence)

    return sentences

def generate_empirical_distributions(empirical_distributions, var_order):
    empirical_sentences = []
    for config, prob in empirical_distributions:
        cond_str = " and ".join(f"({var_order[j]} = {c})" for j, c in enumerate(config))
        empirical_sentences.append(f"{prob} <= P({cond_str}) <= {prob} ; False")
    return empirical_sentences

def generate_twin_network(dag, intervention, unob, variables, verbose=False):
    twin_sentences = []
    observed_var, intervened_var, value = intervention

    modified_edges = {child: [parent for parent in parents if child != intervened_var] for child, parents in dag.items()}
    reachable_nodes = find_connected_nodes(modified_edges, observed_var)

    twin_sentences.append(f"1 <= P({intervened_var}L = {value}) <= 1")
    for var in reachable_nodes:
        if var == intervened_var:
            continue
        if var in dag and var not in unob:
            twin_mechanisms = generate_mechanism(var, dag[var], unob, variables, True, verbose)
            twin_sentences.extend(twin_mechanisms)

    return twin_sentences

def find_connected_nodes(graph, target):
        reachable = set()
        stack = [target]
        while stack:
            node = stack.pop()
            if node not in reachable:
                reachable.add(node)
                stack.extend([n for n in graph.get(node, []) if n not in reachable])
        return reachable

def write_list_to_file_with_index(lst, file_path, header=None):
    n = 0
    with open(file_path, 'r') as file:
        for line in file:
            stripped_line = line.strip()
            if stripped_line and not stripped_line.startswith('#'):
                n += 1
    
    with open(file_path, 'a') as file:
        if header:
            file.write(f"# {header}\n")
        for index, item in enumerate(lst, start=n+1):
            file.write(f"s{index}: {item}\n")
        file.write("\n")

def create_lcn(edges, unob, cardinalities, intervention_input, empirical_distributions, var_order, output_file, verbose=False):
    dag, unob, variables, edges = parse_input(edges, unob, cardinalities)
    calculate_ccomponents(variables, edges, verbose)
    create_auxiliary_exogenous(dag, unob, variables)
    
    print(f"considered DAG: {dag}")
    print(f"considered latent variables: {unob}")
    print(f"considered variables and cardinalities: {variables}\n")

    with open(output_file, 'w') as file:
        file.write("# Generated LCN file\n")
        file.write("\n# Cardinalities\n")
        for index, (variable, cardinality) in enumerate(variables.items()):
            file.write(f"c{index+1}: {variable} <- {cardinality}\n")
        file.write("\n# Mechanisms\n")

    for var in dag:
        if var not in unob:
            mechanism = generate_mechanism(var, dag[var], unob, variables, False, verbose)
            write_list_to_file_with_index(mechanism, output_file)

    empirical_sentences = generate_empirical_distributions(empirical_distributions, var_order)
    write_list_to_file_with_index(empirical_sentences, output_file, "Empirical distributions")

    twin_sentences = generate_twin_network(dag, intervention_input, unob, variables, verbose)
    write_list_to_file_with_index(twin_sentences, output_file, "Twin network")

def main():
    balke_pearl_nonbinary = {
        "edges": "X1 -> X2, X2 -> X3, U -> X2, U -> X3",
        "unob": "X3",
        "intervention_input": ("X3", "X2", 0),
        "cardinalities": {},
        "empirical_distributions": [
            [[0, 0, 0], 0.288],
            [[0, 0, 1], 0.036],
            [[0, 1, 0], 0.288],
            [[0, 1, 1], 0.288],
            [[1, 0, 0], 0.002],
            [[1, 0, 1], 0.067],
            [[1, 1, 0], 0.017],
            [[1, 1, 1], 0.014],
        ],
        "var_order": ["X1", "X2", "X3"],
        "output_file": "./examples/balke_pearl_nonbinary.lcn"
    }

    simple_ccomponent_zhang = {
        "edges": "X1 -> X2, X2 -> X3, U1 -> X1, U1 -> X2, U2 -> X2, U2 -> X3",
        "unob": "U1, U2",
        "intervention_input": ("X3", "X2", 0),
        "cardinalities": {},
        "empirical_distributions": [
            [[0, 0, 0], 0.288],
            [[0, 0, 1], 0.036],
            [[0, 1, 0], 0.288],
            [[0, 1, 1], 0.288],
            [[1, 0, 0], 0.002],
            [[1, 0, 1], 0.067],
            [[1, 1, 0], 0.017],
            [[1, 1, 1], 0.014],
        ],
        "var_order": ["X1", "X2", "X3"],
        "output_file": "./examples/simple_ccomponent_zhang.lcn"
    }

    simple_test = {
        "edges": "X1 -> X3, X2 -> X3",
        "unob": "",
        "intervention_input": ("X3", "X2", 0),
        "cardinalities": {},
        "empirical_distributions": [
            [[0, 0, 0], 0.288],
            [[0, 0, 1], 0.036],
            [[0, 1, 0], 0.288],
            [[0, 1, 1], 0.288],
            [[1, 0, 0], 0.002],
            [[1, 0, 1], 0.067],
            [[1, 1, 0], 0.017],
            [[1, 1, 1], 0.014],
        ],
        "var_order": ["X1", "X2", "X3"],
        "output_file": "./examples/simple_test.lcn"
    }

    create_lcn(**simple_ccomponent_zhang)

if __name__ == "__main__":
    main()
