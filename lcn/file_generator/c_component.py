from .graph import Graph
from .dfsRunner import DfsRunner

class CComponent:
    def __init__(self, nodes=None):
        if nodes is None:
            nodes = []
        self.nodes = nodes

    def find_cComponents(graph: Graph):
        for i in range(1, graph.num_nodes + 1):
            if not graph.visited[i] and graph.cardinalities[i] < 1:            
                graph.curr_nodes.clear()
                DfsRunner.dfs(i, graph)
                graph.dag_components.append(CComponent(graph.curr_nodes[:]))
    