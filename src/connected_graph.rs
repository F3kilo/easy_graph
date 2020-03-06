use crate::Graph;
use std::hash::Hash;

pub struct ConnectedGraph<T: Eq + Hash>(Graph<T>);

impl<T: Eq + Hash + Clone> ConnectedGraph<T>{
    /// Creates `ConnectedGraph<T>` from basic `Graph<T>` by taking it's connected part,
    /// that contains `vertex`.
    pub fn take_connected_part(graph: &mut Graph<T>, vertex: &T) -> Self {
        Self(graph.take_connected_graph(vertex))
    }

    /// Converts basic `Graph<T>` into vector of `ConnectedGraph<T>` with splitting it into
    /// connected parts.
    pub fn split_graph(graph: Graph<T>) -> Vec<Self> {
        graph.into_connected_graphs().into_iter().map(Self).collect()
    }

    /// Converts self into `Graph<T>`
    pub fn into_graph(self) -> Graph<T> {
        self.0
    }

    /// Return immutable reference to underlying graph
    pub fn graph(&self) -> &Graph<T> {
        &self.0
    }

    /// Adds edge to graph. This operation can't make graph not connected.
    pub fn add_edge(&mut self, v1: &T, v2: &T) -> bool {
        self.0.add_edge(v1, v2)
    }

    /// Removes all vertices with single connection.
    /// After that operation, all left vertices will have at least two connections.
    pub fn remove_single_connected(&mut self) {
        self.0.remove_weak_connected(2);
    }
}