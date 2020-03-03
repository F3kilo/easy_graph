# Easy graph
Easy rust realization of generic graph

## Description
Data structure that represent generic **vertices** and undirected **connections**

## Example
```
let verts = vec![0, 1, 2, 3, 4, 10];
let conns = vec![(0, 1), (1, 2), (2, 3), (3, 4), (10, 0), (4, 10)];

let graph = Graph::from_data(verts.into_iter(), conns.into_iter());
assert_eq!(verts.len(), g.len());

let new_vertex = 15;
assert!(graph.add_vertex(new_vertex));
assert!(graph.contains(&new_vertex));

graph.add_edge(&1, &4);
assert!(graph.is_connected(&1, &4));
assert!(graph.is_connected(&4, &1));
```
