from .graph import Graph
class Logger:        
    def debugGraph(graph: Graph):        
        print("debug indexToLabel", graph.cardinalities)        
        for index, label in graph.index_to_label.items():
            print(f"index {index} label {label}")

        print("debug labelToIndex", graph.cardinalities)
        for label, index in graph.label_to_index.items():
            print(f"label {label} index {index}")

        print("Latent variables: \n")
        for i in range(1, graph.num_nodes + 1):
            if graph.cardinalities[i] < 1:
                print(f"latent var {i} with label {graph.index_to_label[i]}")

        print("debugging graph:\n", graph.cardinalities)
        for i in range(1, graph.num_nodes + 1):
            print(f"Edges from {graph.index_to_label[i]}")
            for el in graph.adj[i]:
                print(graph.index_to_label[el] + " ")        

    def debugCcomponents(graph: Graph):        
        for i, component in enumerate(graph.dag_components):
            print(f"c-component #{i + 1}")
            for node in component.nodes:
                status = "Latent" if graph.cardinalities[node] < 1 else "Observable"
                print(f"node {node}({graph.index_to_label[node]}) - {status}")