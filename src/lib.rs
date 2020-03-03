use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

/// Determine default capacity of connections set for every vertex.
pub const DEFAULT_CONNECTIONS_PER_VERTEX: usize = 4;

/// Data structure that represent generic *vertices* and undirected connections
/// between them - *edges*.
#[derive(Clone, Debug, Default)]
pub struct Graph<T: Hash + Eq> {
    verts: HashMap<T, HashSet<T>>,
    edge_per_vertex_capacity: usize,
}

impl<T: Hash + Eq + Clone> Graph<T> {
    /// Creates new empty graph.
    pub fn new() -> Self {
        Self {
            verts: HashMap::new(),
            edge_per_vertex_capacity: DEFAULT_CONNECTIONS_PER_VERTEX,
        }
    }

    /// Creates empty graph with preallocated memory for vertices and edges.
    /// # Arguments:
    /// `vertices_capacity` - capacity for collection of vertices.
    /// `edge_per_vertex_capacity` - capacity for connections collections for each vertex.
    /// Default value `const DEFAULT_CONNECTIONS_PER_VERTEX: usize = 4`
    pub fn with_capacity(vertices_capacity: usize, edge_per_vertex_capacity: usize) -> Self {
        Self {
            verts: HashMap::with_capacity(vertices_capacity),
            edge_per_vertex_capacity,
        }
    }

    /// Creates graph filled by `vertices` with `edges`.
    /// # Arguments:
    /// `vertices` - iterator of vertices.
    /// `edges` - iterator of pairs of vertices indices, which must be connected.
    pub fn from_data(
        vertices: impl Iterator<Item=T>,
        edges: impl Iterator<Item=(T, T)>,
    ) -> Self {
        let verts: HashMap<T, HashSet<T>> = vertices
            .map(|v| (v, HashSet::with_capacity(DEFAULT_CONNECTIONS_PER_VERTEX)))
            .collect();

        let mut temp = Self {
            verts,
            edge_per_vertex_capacity: DEFAULT_CONNECTIONS_PER_VERTEX,
        };

        for (v1, v2) in edges {
            temp.add_edge(&v1, &v2);
        }

        temp
    }

    /// Tests if graph contains `v`.
    pub fn contains(&self, v: &T) -> bool {
        self.verts.contains_key(v)
    }

    /// Adds vertex to graph.
    /// # Arguments:
    /// `vertex` - vertex, that must be added.
    /// # Returns:
    /// `true` if vertex is new and was really added
    pub fn add_vertex(&mut self, v: T) -> bool {
        if self.verts.contains_key(&v) {
            return false;
        }
        self.verts
            .insert(v, HashSet::with_capacity(self.edge_per_vertex_capacity));
        true
    }

    /// Adds edge to graph.
    /// # Arguments:
    /// `v1` - vertex, that will be connected with `v2`.
    /// `v2` - vertex, that will be connected with `v1`.
    /// # Returns:
    /// `true` if edge was added actualy;
    /// `false` if edge was presented already;
    pub fn add_edge(&mut self, v1: &T, v2: &T) -> bool {
        if self.verts.contains_key(v1) && self.verts.contains_key(v2) {
            if v1 == v2 {
                return false;
            }
            self.verts.get_mut(v1).unwrap().insert(v2.clone());
            self.verts.get_mut(v2).unwrap().insert(v1.clone());
            return true;
        }
        false
    }

    /// Removes edge from graph.
    /// If edge is not present, that function does nothing.
    /// # Arguments:
    /// `v1` - vertex, that will be disconnected with `v2`.
    /// `v2` - vertex, that will be disconnected with `v1`.
    /// # Returns:
    /// `true` if edge was removed actualy;
    /// `false` if edge wasn't presented already;
    pub fn remove_edge(&mut self, v1: &T, v2: &T) -> bool {
        if self.verts.contains_key(v1) && self.verts.contains_key(v2) {
            self.verts.get_mut(v1).unwrap().remove(v2);
            self.verts.get_mut(v2).unwrap().remove(v1);
            return true;
        }
        false
    }

    /// Checks if edge, that connects specified vertices, is present.
    /// Connections are undirectional, thats why always
    /// `is_connected(v1, v2) == is_connected(v2, v1)`
    /// # Arguments:
    /// `v1` - first vertex to check.
    /// `v2` - second vertex to check.
    pub fn is_connected(&self, v1: &T, v2: &T) -> bool {
        if let Some(v) = self.verts.get(v1) {
            if v1 == v2 {
                return true;
            }
            return v.contains(v2);
        }
        false
    }

    /// Connects of vertices with specified index.
    /// # Arguments:
    /// `v` - vertex of interest;
    /// # Returns:
    /// Set of vertices, that connected to `v`, or None if `v` is not in graph.
    pub fn connects_of(&self, v: &T) -> Option<&HashSet<T>> {
        self.verts.get(v)
    }

    /// Iterator of all current vertices.
    pub fn vertices(&self) -> impl Iterator<Item=&T> {
        self.verts.keys()
    }

    /// Current count of vertices.
    pub fn len(&self) -> usize {
        self.verts.len()
    }

    /// True, if graph does not contain vertices.
    pub fn is_empty(&self) -> bool {
        self.verts.is_empty()
    }
}

impl<T: Eq + Hash> PartialEq<Graph<T>> for Graph<T> {
    fn eq(&self, other: &Graph<T>) -> bool {
        self.verts == other.verts
    }
}

impl<T: Eq + Hash> Eq for Graph<T> {}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_data() -> (Vec<i32>, Vec<(i32, i32)>) {
        let verts = vec![0, 1, 2, 3, 4, 10];
        let conns = vec![(0, 1), (1, 2), (2, 3), (3, 4), (10, 0), (4, 10), ];
        (verts, conns)
    }

    fn test_graph() -> Graph<i32> {
        let (verts, conns) = test_data();
        Graph::from_data(verts.into_iter(), conns.into_iter())
    }

    #[test]
    fn from_data() {
        let verts = test_data().0;
        let g = test_graph();

        assert_eq!(verts.len(), g.len());

        assert!(g.contains(&0));
        assert!(g.contains(&1));
        assert!(g.contains(&2));
        assert!(g.contains(&3));
        assert!(g.contains(&4));
        assert!(g.contains(&10));

        assert!(g.is_connected(&0, &10));
        assert!(g.is_connected(&0, &1));
        assert!(g.is_connected(&1, &0));
        assert!(g.is_connected(&1, &2));
        assert!(g.is_connected(&2, &3));
        assert!(g.is_connected(&2, &1));
        assert!(g.is_connected(&3, &2));
        assert!(g.is_connected(&3, &4));
        assert!(g.is_connected(&4, &3));
        assert!(g.is_connected(&4, &10));
        assert!(g.is_connected(&10, &0));
        assert!(g.is_connected(&10, &4));
    }

    #[test]
    fn add_vertex() {
        let mut g = test_graph();
        let new_vertex = 15;
        assert!(g.add_vertex(new_vertex));
        let presented_vertex = 3;
        assert!(!g.add_vertex(presented_vertex));
        assert!(g.contains(&new_vertex));
        assert!(g.contains(&presented_vertex));
        assert!(g.connects_of(&new_vertex).unwrap().is_empty());
        assert_eq!(g.connects_of(&presented_vertex).unwrap().len(), 2);
    }

    #[test]
    fn add_edge() {
        let mut g = test_graph();
        g.add_edge(&1, &4);
        assert!(g.is_connected(&1, &4));
        assert!(g.is_connected(&4, &1));
    }

    #[test]
    fn remove_edge() {
        let mut g = test_graph();
        assert!(g.remove_edge(&0, &1));
        assert!(!g.is_connected(&0, &1));
        assert!(!g.is_connected(&1, &0));
        g.remove_edge(&1, &0);
    }
}