from .graph import Graph

class DfsRunner:            
    def dfs(node: int, graph: Graph):
        graph.visited[node] = True
        graph.curr_nodes.append(node)
        is_observable = graph.cardinalities[node] > 1

        if not is_observable:
            for adj_node in graph.adj[node]:
                if not graph.visited[adj_node]:
                    DfsRunner.dfs(adj_node, graph)
        else:
            for parent_node in graph.parents[node]:
                if not graph.visited[parent_node] and graph.cardinalities[parent_node] < 1:
                    DfsRunner.dfs(parent_node, graph)
