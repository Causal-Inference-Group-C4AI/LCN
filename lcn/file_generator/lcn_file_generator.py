# Doesn't work for systems where an endogenous has more than one exogenous parent

from itertools import product

def parse_input(edges_str, unob_str):
    edges = edges_str.split(", ")
    unob = unob_str.split(", ") if unob_str else []

    dag = {}
    children = {}

    for edge in edges:
        parent, child = edge.split(" -> ")
        if child in dag:
            dag[child].append(parent)
        else:
            dag[child] = [parent]
        if parent not in dag:
            dag[parent] = []
        if parent not in children:
            children[parent] = []
        children[parent].append(child)

    print("Parsed DAG:", dag)
    return dag, unob, children

# Identify endogenous variables without exogenous parents and create auxiliary exogenous variables
def create_auxiliary_exogenous(dag, unob, children):
    auxiliary_exo_vars = []
    for child, parents in dag.items():
        if (child not in unob) and (not any(p in unob for p in parents)):
            aux_exo = f"Uaux_{child}"
            unob.append(aux_exo)
            auxiliary_exo_vars.append(aux_exo)
            dag[child].append(aux_exo)
            if aux_exo not in children:
                children[aux_exo] = [child]  # Add to children dictionary for decomposition
            else:
                children[aux_exo].append(child)
    return auxiliary_exo_vars


# Binarize exogenous variables by decomposing them into subvariables
def binarize_exogenous(dag, exo_vars, children):
    decompositions = {}
    total_decompositions = {}

    for exo_var in exo_vars[:]:
        exo_decomps = 0
        decompositions[exo_var] = {}
        
        for child in children.get(exo_var, []):
            endogenous_parents = [p for p in dag.get(child, []) if p != exo_var]
            num_parents = len(endogenous_parents)
            required_decomps = 2 ** num_parents
            decompositions[exo_var][child] = required_decomps

            decomposed_vars = [f"{exo_var}_{exo_decomps+i+1}" for i in range(required_decomps)]
            dag[child].extend(decomposed_vars)
            exo_vars.extend(decomposed_vars)
            dag[child].remove(exo_var)

            exo_decomps += required_decomps

        total_decompositions[exo_var] = exo_decomps
        exo_vars.remove(exo_var)

    print(f"Decompositions: {decompositions}")
    print(f"Total decompositions: {total_decompositions}")

    exo_var_map = {}
    for exo_var, total in total_decompositions.items():
        exo_var_map[exo_var] = [f"{exo_var}_{i+1}" for i in range(total)]

    print(f"considered exogenous subvariable mappings: {exo_var_map}")
    print(f"exo_vars: {exo_vars}")

    return exo_var_map

def generate_mechanism(var, parents, unob, twin=False):
    mechanisms = []
    endogenous_parents = [p for p in parents if p not in unob]
    exogenous_parents = [p for p in parents if p in unob]
    print(f"var: {var}")
    print(f"dag[var]: {parents}")
    print(f"endogenous_parents: {endogenous_parents}")
    print(f"exogenous_parents: {exogenous_parents}")

    if exogenous_parents:
        conditions = list(product([0, 1], repeat=len(endogenous_parents) + len(exogenous_parents)))
        exo_value_index = 0
        for condition in conditions:
            endo_condition = condition[len(exogenous_parents):]
            exo_condition = condition[:len(exogenous_parents)]

            endo_str = " and ".join(f"!{p}L" if c == 0 else f"{p}L" for p, c in zip(endogenous_parents, endo_condition)) if twin else " and ".join(f"!{p}" if c == 0 else p for p, c in zip(endogenous_parents, endo_condition))
            exo_str = " and ".join(f"!{p}" if c == 0 else p for p, c in zip(exogenous_parents, exo_condition))
            cond_str = f"{exo_str} and {endo_str}" if endo_str and exo_str else (endo_str or exo_str)
            
            var_value = exo_condition[exo_value_index]
            mech_str = f"{var_value} <= P({var}L | {cond_str}) <= {var_value}" if twin else f"{var_value} <= P({var} | {cond_str}) <= {var_value}"
            mechanisms.append(mech_str)

            exo_value_index = (exo_value_index + 1) % len(exogenous_parents)

    return mechanisms

def generate_exogenous_dependencies(exo_var_map):
    exo_sentences = []
    for exo_var, subvars in exo_var_map.items():
        for i in range(1, len(subvars)):
            conditions = " or ".join(subvars[:i])
            exo_sentences.append(f"0 <= P({subvars[i]} | {conditions}) <= 1")
    return exo_sentences

def generate_empirical_distributions(empirical_distributions, var_order):
    empirical_sentences = []
    for i, (config, prob) in enumerate(empirical_distributions):
        cond_str = " and ".join(f"{'!' if c == 0 else ''}{var_order[j]}" for j, c in enumerate(config))
        empirical_sentences.append(f"{prob} <= P({cond_str}) <= {prob} ; False")
    return empirical_sentences

def generate_twin_network(dag, intervention, unob):
    twin_sentences = []
    observed_var, intervened_var, value = intervention
    twin_var_intervened = f"{intervened_var}L"
    twin_var_observed = f"{observed_var}L"

    modified_edges = {child: [parent for parent in parents if child != intervened_var] for child, parents in dag.items()}
    reachable_nodes = find_connected_nodes(modified_edges, observed_var)

    twin_sentences.append(f"1 <= P({'!' if value == 0 else ''}{twin_var_intervened}) <= 1")
    for var in reachable_nodes:
        if var == intervened_var:
            continue  # Skip intervened variable
        if var in dag and var not in unob:
            twin_mechanisms = generate_mechanism(var, dag[var], unob, twin=True)
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
    # Step 1: Count the number of non-blank lines that don't start with '#'
    n = 0
    with open(file_path, 'r') as file:
        for line in file:
            stripped_line = line.strip()
            if stripped_line and not stripped_line.startswith('#'):
                n += 1
    
    # Step 2: Write each item of the list to the file with the indexed prefix
    with open(file_path, 'a') as file:
        if header:
            file.write(f"\n# {header}\n")
        for index, item in enumerate(lst, start=n+1):
            file.write(f"s{index}: {item}\n")

def create_lcn(edges, unob, intervention_input, empirical_distributions, var_order, output_file):
    dag, unob, children = parse_input(edges, unob)
    aux_exo_vars = create_auxiliary_exogenous(dag, unob, children)
    exo_var_map = binarize_exogenous(dag, unob, children)
    
    print(f"considered DAG: {dag}")
    print(f"considered unobserved variables: {unob}")
    print(f"considered children: {children}")

    with open(output_file, 'w') as file:
        file.write("# Generated LCN file\n\n")
        file.write("# Mechanisms\n")

    for var in dag:
        if var not in unob:
            mechanism = generate_mechanism(var, dag[var], unob, twin=False)
            write_list_to_file_with_index(mechanism, output_file)

    exo_sentences = generate_exogenous_dependencies(exo_var_map)
    write_list_to_file_with_index(exo_sentences, output_file, "Dependencies between exogenous subvariables")

    empirical_sentences = generate_empirical_distributions(empirical_distributions, var_order)
    write_list_to_file_with_index(empirical_sentences, output_file, "Empirical distributions")

    twin_sentences = generate_twin_network(dag, intervention_input, unob)
    write_list_to_file_with_index(twin_sentences, output_file, "Twin network")

def main():
    edges = "X1 -> X2, X2 -> X3, X3 -> X4, U -> X3, U -> X4, T -> X1"
    unob = "U, T"
    intervention_input = ("X4", "X2", 0) # P(X4 | do(X2 = 0))
    empirical_distributions = [
        [[0, 0, 0], 0.288],
        [[0, 0, 1], 0.036],
        [[0, 1, 0], 0.288],
        [[0, 1, 1], 0.288],
        [[1, 0, 0], 0.002],
        [[1, 0, 1], 0.067],
        [[1, 1, 0], 0.017],
        [[1, 1, 1], 0.014],
    ]
    var_order = ["X1", "X2", "X3"]
    output_file = "./examples/output.lcn"

    create_lcn(edges, unob, intervention_input, empirical_distributions, var_order, output_file)

if __name__ == "__main__":
    main()