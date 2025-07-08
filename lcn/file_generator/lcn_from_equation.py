import itertools
import re

def evaluate_expression(expr, values):
    """
    Evaluate a logical expression with given variable values.

    expr: The logical expression as a string.
    values: A dictionary with variable names as keys and their binary values as values.
    """
    expr = expr.upper()
    
    # Replace variables with their values (0 or 1)
    for var, val in values.items():
        expr = expr.replace(var, str(val))
    
    # Replace logical operators with Python equivalents
    expr = expr.replace("!", " not ").replace("AND", " and ").replace("OR", " or ")
    
    # Simplify double negations in the expression (i.e., !!A -> A)
    while '!!' in expr:
        expr = expr.replace('!!', '')
    
    # Evaluate the expression
    try:
        return eval(expr)
    except Exception as e:
        print(f"Error evaluating expression: {expr}\nException: {e}")
        return False

def compute_conditional_probabilities_to_file(equations, filename):
    """
    Compute the conditional probabilities of the left-hand side of each equation
    given all permutations of the right-hand side variables and print the results in the correct format.
    
    equations: A list of logical equations as strings.
    filename: The name of the file to write the results to.
    """
    with open(filename, 'w') as file:
        index = 1
        for equation in equations:
            # Split the equation into LHS and RHS
            lhs, rhs = equation.split("=")
            lhs = lhs.strip()
            rhs = rhs.strip()
            
            # Find all variables on the right-hand side while preserving order
            variables = re.findall(r'\b[A-Z]\d*\b', rhs)
            unique_variables = list(dict.fromkeys(variables))  # Preserve order and remove duplicates
            
            # Generate all possible permutations of binary values for these variables
            num_vars = len(unique_variables)
            all_permutations = list(itertools.product([0, 1], repeat=num_vars))
            
            for perm in all_permutations:
                values = dict(zip(unique_variables, perm))
                
                rhs_result = evaluate_expression(rhs, values)
                probability = 1.0 if rhs_result else 0.0
                
                # Format the AND expression with the variables' values in the correct order
                and_conditions = ' and '.join([f"!{var}" if values[var] == 0 else var for var in unique_variables])
                
                file.write(f"s{index}: {probability:.0f} <= P({lhs} | {and_conditions}) <= {probability:.0f}\n")
                
                index += 1

# Example usage
equations = [
    "X2 = (X1 and U2) or U3 or U4",
    "X3 = (!X2 and (U1 or U2)) or (X2 and U4)",
]
filename = "/home/ainoue/LCN/examples/probability_ranges_v3.lcn"
compute_conditional_probabilities_to_file(equations, filename)
