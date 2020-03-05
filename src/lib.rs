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

    /// Removes vertex from graph.
    /// # Arguments:
    /// `vertex` - vertex, that must be removed.
    /// # Returns:
    /// If vertex exist, than set of its connections. Else `None`.
    pub fn remove_vertex(&mut self, v: &T) -> Option<HashSet<T>> {
        if let Some(connections) = self.verts.remove(v) {
            for c in &connections {
                self.verts.get_mut(c).unwrap().remove(v);
            }
            return Some(connections);
        }

        None
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

    /// Removes all points, that have less connections than `weak_level`.
    /// In other words, only vertices with more or equal connections than `weak_level`
    /// remains. Complexity: `O(n)`
    /// # Returns:
    /// Set of removed vertices
    /// # Example:
    /// ```
    /// use easy_graph::Graph;
    /// let verts = vec![0,1,2,3];
    /// let conns = vec![(0, 1), (1, 2), (2, 0), (2, 3)];
    /// let mut graph = Graph::from_data(verts.into_iter(), conns.into_iter());
    /// graph.remove_weak_connected(2);
    /// assert_eq!(graph.len(), 3);
    /// assert!(graph.contains(&0));
    /// assert!(graph.contains(&1));
    /// assert!(graph.contains(&2));
    /// assert!(!graph.contains(&3));
    /// assert!(!graph.connects_of(&2).unwrap().contains(&3));
    /// ```
    pub fn remove_weak_connected(&mut self, weak_level: usize) -> HashSet<T> {
        let mut to_process: HashSet<T> = self.verts.iter()
            .filter(|(_, c)| c.len() < weak_level)
            .map(|(v, _)| v.clone()).collect();

        let mut all_removed = HashSet::with_capacity(self.len());

        while !to_process.is_empty() {
            let processing = to_process;
            to_process = HashSet::with_capacity(processing.len() * 4);
            for v in processing {
                if self.contains(&v) {
                    let removed_vert_neighbors = self.remove_vertex(&v).unwrap();
                    all_removed.insert(v);
                    let weak_connected_neighbors = removed_vert_neighbors
                        .into_iter()
                        .filter(|n| self.connects_of(n).unwrap().len() < weak_level);
                    to_process.extend(weak_connected_neighbors);
                }
            }
        }
        all_removed
    }

    /// Returns set of vertices, for which exists path to `vertex`.
    pub fn verts_with_path_to(&self, vertex: &T) -> HashSet<T> {
        let mut to_process = HashSet::with_capacity(self.len());
        to_process.insert(vertex.clone());
        let mut separate_part_verts = HashSet::with_capacity(self.len());
        while !to_process.is_empty() {
            let to_process_iter = to_process.into_iter();
            to_process = HashSet::with_capacity(self.len());
            for v in to_process_iter {
                let connections_iter = self.verts.get(&v).unwrap().clone().into_iter();
                to_process.extend(connections_iter.filter(|c| !separate_part_verts.contains(c)));
                separate_part_verts.insert(v);
            }
        }
        separate_part_verts
    }

    /// Takes connected graph that contains `vertex`.
    pub fn take_connected_graph(&mut self, vertex: &T) -> Self {
        if !self.verts.contains_key(vertex) {
            return Self::new();
        }

        let separate_part_verts = self.verts_with_path_to(vertex);

        let mut separate_part = Self::with_capacity(self.len(), self.edge_per_vertex_capacity);
        for v in separate_part_verts {
            let (v, c) = self.verts.remove_entry(&v).unwrap();
            separate_part.verts.insert(v, c);
        }

        separate_part
    }

    /// Split `self` into connected graphs.
    pub fn into_connected_graphs(mut self) -> Vec<Self> {
        let separate_part_capacity = 4;
        let mut separate_parts = Vec::with_capacity(separate_part_capacity);
        while !self.is_empty() {
            let start = self.verts.iter().next().unwrap().0.clone();
            separate_parts.push(self.take_connected_graph(&start));
        }

        separate_parts
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

        assert_test_data(g);
    }

    fn assert_test_data(g: Graph<i32>) {
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
    fn remove_vertex() {
        let mut g = test_graph();
        assert!(g.remove_vertex(&22).is_none());
        let c = g.remove_vertex(&2);
        assert!(c.is_some());
        let c = c.unwrap();
        assert_eq!(c.len(), 2);
        assert!(c.contains(&1));
        assert!(c.contains(&3));
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

    #[test]
    fn remove_weak_connected() {
        let mut g = test_graph();
        g.add_vertex(11);
        g.add_vertex(12);
        g.add_edge(&0, &11);
        g.add_edge(&11, &12);
        g.add_edge(&2, &4);
        g.add_edge(&10, &3);
        g.add_edge(&10, &2);
        g.add_edge(&1, &2);
        assert_eq!(g.len(), 8);
        g.remove_weak_connected(2);
        assert_eq!(g.len(), 6);
        assert!(g.contains(&0));
        assert!(g.contains(&1));
        assert!(g.contains(&2));
        assert!(g.contains(&3));
        assert!(g.contains(&4));
        assert!(g.contains(&10));
        g.remove_weak_connected(3);
        assert_eq!(g.len(), 4);
        assert!(g.contains(&2));
        assert!(g.contains(&3));
        assert!(g.contains(&4));
        assert!(g.contains(&10));
    }


    #[test]
    fn verts_with_path_to() {
        let mut g = test_graph();
        g.add_vertex(20);
        g.add_vertex(30);
        g.add_vertex(40);
        g.add_edge(&20, &30);
        g.add_edge(&30, &40);
        g.add_edge(&40, &20);

        let cg1 = g.verts_with_path_to(&0);
        let cg2 = g.verts_with_path_to(&20);

        assert_eq!(cg1.len(), 6);
        assert_eq!(cg2.len(), 3);

        assert!(cg1.contains(&0));
        assert!(cg1.contains(&1));
        assert!(cg1.contains(&2));
        assert!(cg1.contains(&3));
        assert!(cg1.contains(&4));
        assert!(cg1.contains(&10));

        assert!(cg2.contains(&20));
        assert!(cg2.contains(&30));
        assert!(cg2.contains(&40));
    }

    #[test]
    fn take_connected_graph() {
        let mut g = test_graph();
        g.add_vertex(20);
        g.add_vertex(30);
        g.add_vertex(40);
        g.add_edge(&20, &30);
        g.add_edge(&30, &40);
        g.add_edge(&40, &20);

        assert!(g.take_connected_graph(&50).is_empty());
        assert_eq!(g.len(), 9);

        let sp = g.take_connected_graph(&20);
        assert_eq!(g.len(), 6);
        assert_eq!(sp.len(), 3);

        assert_test_data(g);

        assert_separate_part(sp);
    }

    fn assert_separate_part(sp: Graph<i32>) {
        assert!(sp.contains(&20));
        assert!(sp.contains(&30));
        assert!(sp.contains(&40));
        assert!(sp.is_connected(&20, &30));
        assert!(sp.is_connected(&30, &40));
        assert!(sp.is_connected(&40, &20));
    }

    #[test]
    fn into_connected_graphs() {
        let mut g = test_graph();
        g.add_vertex(20);
        g.add_vertex(30);
        g.add_vertex(40);
        g.add_edge(&20, &30);
        g.add_edge(&30, &40);
        g.add_edge(&40, &20);

        let mut  separate_parts = g.into_connected_graphs();
        assert_eq!(separate_parts.len(), 2);

        if separate_parts[0].contains(&20) {
            assert_test_data(separate_parts.remove(1));
            assert_separate_part(separate_parts.remove(0));
        } else {
            assert_separate_part(separate_parts.remove(1));
            assert_test_data(separate_parts.remove(0));
        }
    }
}