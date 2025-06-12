package com.thealgorithms.datastructures.graphs;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.HashMap;
import java.util.PriorityQueue;
import java.util.Collections;

// Contraction Hiearchies Algorithm
// https://en.wikipedia.org/wiki/Contraction_hierarchies
// https://jeansebastien-gonsette.medium.com/routing-faster-than-dijkstra-thanks-to-contraction-hierarchies-232302345921
//
// Bidirectional Dijksta's
// https://en.wikipedia.org/wiki/Dijkstra's_algorithm
// https://en.wikipedia.org/wiki/Bidirectional_search

class Vertex implements Comparable {
    int id;
    int adjContracted;

    Vertex(int id) {
        this.id = id;
        this.adjContracted = 0;
    }

    public int compareTo(Object obj) {
        Vertex other = (Vertex) obj;
        return id - other.id;
    }
}

class Edge {
    public enum Direction {
        forward, backward
    };

    Direction direction;
    Vertex to;
    int weight;

    Edge(Vertex to, int weight, Direction direction) {
        this.to = to;
        this.weight = weight;
        this.direction = direction;
    }
}

class Shortcut extends Edge {
    int level;
    Vertex contracted;

    Shortcut(Vertex to, int weight, Direction direction, Vertex contracted, int level) {
        super(to, weight, direction);
        this.level = level;
        this.contracted = contracted;
    }
}

class GraphAdjList {
    HashMap<Integer, Vertex> vertices;
    HashMap<Vertex, ArrayList<Edge>> adjList;

    GraphAdjList() {
        vertices = new HashMap<>();
        adjList = new HashMap<>();
    }

    // node id's are distinct
    // In query phase, forward search goes from low id to high id
    // likewise, backward search goes from high id to low id
    // so when adding edges, first argument should be the lower id, second one the
    // higher id
    void AddEdge(int ID1, int ID2, int weight) {
        if (ID1 < 0 || ID2 < 0)
            throw new IllegalArgumentException("Id's must be positive integers");

        if (ID1 == ID2)
            throw new IllegalArgumentException("No self loops");

        if (weight < 1)
            throw new IllegalArgumentException("Edge weights must be positive integers");

        // swap id's to maintain id ordering
        if (ID1 > ID2) {
            ID1 = ID1 ^ ID2;
            ID2 = ID1 ^ ID2;
            ID1 = ID1 ^ ID2;
        }

        if (vertices.get(ID1) == null) {
            vertices.put(ID1, new Vertex(ID1));
            adjList.put(vertices.get(ID1), new ArrayList<Edge>());
        }
        if (vertices.get(ID2) == null) {
            vertices.put(ID2, new Vertex(ID2));
            adjList.put(vertices.get(ID2), new ArrayList<Edge>());
        }

        Vertex v1 = vertices.get(ID1);
        Vertex v2 = vertices.get(ID2);

        adjList.get(v1).add(new Edge(v2, weight, Edge.Direction.forward));
        adjList.get(v2).add(new Edge(v1, weight, Edge.Direction.backward));
    }
}

class CH {
    GraphAdjList graph;
    HashMap<Vertex, ArrayList<Shortcut>> shortcuts;
    int shortcutCount;

    CH(GraphAdjList graph) {
        this.graph = graph;
        this.shortcuts = new HashMap<>();
        this.shortcutCount = 0;
        PreProcessGraph();
    }

    class Kvp<T> implements Comparable {
        int key;
        T val;

        Kvp(int key, T val) {
            this.key = key;
            this.val = val;
        }

        public int compareTo(Object obj) {
            Kvp<T> other = (Kvp<T>) obj;
            return key - other.key;
        }

        public int getKey() {
            return key;
        }

        public T getVal() {
            return val;
        }
    }

    private void RelaxEdges(Vertex u, PriorityQueue<Kvp<Vertex>> minPQ, HashMap<Vertex, Integer> dist,
            HashMap<Vertex, Vertex> pred, Edge.Direction direction) {
        HashSet<Shortcut> relaxedShortcuts = new HashSet<>();
        var sCuts = shortcuts.get(u);
        if (sCuts != null) {
            int highestLevel = -1;
            for (Shortcut s : sCuts) {
                if (s.level > highestLevel && s.direction == direction)
                    highestLevel = s.level;
            }

            // relax shortcuts with given direction that lead to higher-level nodes
            for (Shortcut s : sCuts) {
                if (s.level < highestLevel || s.direction != direction)
                    continue;

                Vertex w = s.to;
                int weight = s.weight;

                // relax shortcut
                int uDist = dist.getOrDefault(u, 0);
                if (!dist.containsKey(w) || uDist + weight < dist.get(w)) {
                    dist.put(w, uDist + weight);
                    pred.put(w, u);
                    minPQ.add(new Kvp<Vertex>(dist.get(w), w));
                    relaxedShortcuts.add(s);
                }
            }
        }

        // relax edges with given direction that lead to higher-level nodes
        for (Edge edge : graph.adjList.get(u)) {
            if (edge.direction != direction)
                continue;

            Vertex w = edge.to;
            int weight = edge.weight;

            // skip current edge if its 'to' vertex (w) is on a lower level than the 'from'
            // vertex (u)
            boolean skipEdge = false;
            Iterator<Shortcut> it = relaxedShortcuts.iterator();
            ArrayList<Vertex> path = new ArrayList<>();
            while (it.hasNext()) {
                Shortcut s = it.next();
                UnpackPathReversed(u, s.to, path, pred);
                for (Vertex vert : path) {
                    if (vert == w) {
                        skipEdge = true;
                        break;
                    }
                }
                if (skipEdge)
                    break;
                path.clear();
            }
            if (skipEdge)
                continue;

            // relax edge
            int uDist = dist.getOrDefault(u, 0);
            if (!dist.containsKey(w) || uDist + weight < dist.get(w)) {
                dist.put(w, uDist + weight);
                pred.put(w, u);
                minPQ.add(new Kvp<Vertex>(dist.get(w), w));
            }
        }
    }

    private void ReconstructReversedPath(Vertex from, Vertex to, HashMap<Vertex, Vertex> pred, ArrayList<Vertex> path) {
        Vertex curr = to;
        while (curr != from) {
            path.add(curr);
            curr = pred.get(curr);
        }
    }

    private ArrayList<Vertex> ForwardDijkstra(Vertex from, Vertex to, HashMap<Vertex, Integer> dist,
            HashMap<Vertex, Vertex> pred) {
        if (from.id > to.id) // maintain low to high id ordering for forward search
        {
            Vertex tmp = from;
            from = to;
            to = tmp;
        }

        PriorityQueue<Kvp<Vertex>> minPQ = new PriorityQueue<>();
        minPQ.add(new Kvp<Vertex>(0, from));

        while (!minPQ.isEmpty()) {
            Vertex u = minPQ.poll().val;
            if (u == to)
                break;
            RelaxEdges(u, minPQ, dist, pred, Edge.Direction.forward);
        }

        // note: we're not unpacking any shortcuts
        ArrayList<Vertex> path = new ArrayList<>();
        ReconstructReversedPath(from, to, pred, path);
        return path;
    }

    /**
     * for preprocessing stage
     * used to skip any pair where one of the nodes is the contracted node for a
     * shortcut
     * i.e. where one is on a lower contracted level
     * a contracted node that has more than 1 neighbor HAS to be part of a shortcut
     * 
     * @param from
     * @param vertsToContract
     * @return
     */
    private boolean IsContractedForShortcut(Vertex v, HashSet<Vertex> vertsToContract) {
        return graph.adjList.get(v).size() > 1 && !vertsToContract.contains(v);
    }

    private int WitnessSearch(Vertex from, Vertex to, Vertex contractVert, HashSet<Vertex> vertsToContract) {
        // check shortest path (u, w) for contracted node 'v'
        if (!IsContractedForShortcut(from, vertsToContract) &&
                !IsContractedForShortcut(to, vertsToContract)) {
            HashMap<Vertex, Integer> dist = new HashMap<>();
            HashMap<Vertex, Vertex> pred = new HashMap<>();
            ArrayList<Vertex> path = ForwardDijkstra(from, to, dist, pred);

            // calculate weight of shortcut if shortest path contains the contracted node
            for (int i = 0; i < path.size(); i++) {
                // since path is reversed, target vertex is at 0th index
                // (no matter the initial id order of 'from' and 'to')
                // weight of shortcut is dist between 'from' and 'to, or dist[target vertex]
                if (path.get(i) == contractVert)
                    return dist.get(path.get(0));
            }
        }

        return -1;
    }

    Vertex[] GetNeighbors(Vertex v) {
        // include direct (forward and backward) and shortcut neighbors
        var edges = graph.adjList.get(v);
        var sCuts = shortcuts.get(v);
        Integer edgesCount = edges != null ? edges.size() : 0;
        Integer sCutCount = sCuts != null ? sCuts.size() : 0;
        Vertex[] adjVerts = new Vertex[edgesCount + sCutCount];

        int i = 0;
        for (int j = 0; j < edgesCount; j++)
            adjVerts[i++] = edges.get(j).to;
        for (int j = 0; j < sCutCount; j++)
            adjVerts[i++] = sCuts.get(j).to;

        return adjVerts;
    }

    private void ContractVertex(Vertex v, HashSet<Vertex> vertsToContract) {
        Vertex[] adjVerts = GetNeighbors(v);

        for (int i = 0; i < adjVerts.length - 1; i++) {
            for (int j = i + 1; j < adjVerts.length; j++) {
                Vertex u = adjVerts[i];
                Vertex w = adjVerts[j];

                int pathDist = WitnessSearch(u, w, v, vertsToContract);
                if (pathDist > 0) {
                    var uDir = u.id < w.id ? Edge.Direction.forward : Edge.Direction.backward;
                    var wDir = uDir == Edge.Direction.forward ? Edge.Direction.backward : Edge.Direction.forward;

                    if (shortcuts.get(u) == null)
                        shortcuts.put(u, new ArrayList<Shortcut>());
                    if (shortcuts.get(w) == null)
                        shortcuts.put(w, new ArrayList<Shortcut>());

                    shortcuts.get(u).add(new Shortcut(w, pathDist, uDir, v, shortcutCount));
                    shortcuts.get(w).add(new Shortcut(u, pathDist, wDir, v, shortcutCount));
                    shortcutCount++; // forward and backward directions count as 1 shortcut
                }
            }
        }

        // incrementing counters for direct neighbors
        // inner if statement ensures we don't increment counters for contracted nodes,
        // but it isn't really necessary
        var adjDirect = graph.adjList.get(v);
        for (int i = 0; i < adjDirect.size(); i++) {
            if (vertsToContract.contains(adjDirect.get(i).to))
                adjDirect.get(i).to.adjContracted++;
        }

        vertsToContract.remove(v);
    }

    private Vertex ChooseNextVertex(HashSet<Vertex> vertsToContract) {
        Vertex nextVert = vertsToContract.iterator().next();
        double minShortcutCounter = Double.POSITIVE_INFINITY;

        for (var v : vertsToContract) {
            // include direct and shortcut neighbors, forwards and backwards
            Vertex[] adjVerts = GetNeighbors(v);

            // get node w/ smallest counter of nearby contracted nodes
            // and creates minimal shortucts when contracted
            if (v.adjContracted <= nextVert.adjContracted) {
                int shortcutCounter = 0;
                for (int i = 0; i < adjVerts.length - 1; i++) {
                    for (int j = i + 1; j < adjVerts.length; j++) {
                        Vertex u = adjVerts[i];
                        Vertex w = adjVerts[j];

                        if (WitnessSearch(u, w, v, vertsToContract) > 0)
                            shortcutCounter++;
                    }
                }

                if (shortcutCounter < minShortcutCounter) {
                    nextVert = v;
                    minShortcutCounter = shortcutCounter;
                }
            }
        }

        return nextVert;
    }

    /**
     * create shortcuts; bottom-up approach
     * 
     * @param graph
     */
    private void PreProcessGraph() {
        HashSet<Vertex> vertsToContract = new HashSet<>(graph.adjList.keySet());

        Vertex curr;
        while (!vertsToContract.isEmpty()) {
            curr = ChooseNextVertex(vertsToContract);
            ContractVertex(curr, vertsToContract);
        }
    }

    private void UnpackPathReversed(Vertex from, Vertex to, ArrayList<Vertex> path, HashMap<Vertex, Vertex> pred) {
        Vertex curr = to;
        while (curr != from) {
            // unpack any shortcut(s)
            Vertex prev = pred.get(curr);
            while (curr != prev) {
                path.add(curr);

                boolean sCutFound = false;
                var sCuts = shortcuts.get(curr);
                if (sCuts != null) {
                    for (Shortcut s : sCuts) {
                        if (s.to == prev) {
                            sCutFound = true;
                            curr = s.contracted;
                            break;
                        }
                    }
                }
                if (!sCutFound)
                    curr = prev;
            }
        }
    }

    private void ConstructPathBidirectional(Vertex from, Vertex lastFwd, Vertex lastBck, Vertex to,
            HashMap<Vertex, Vertex> predFwd, HashMap<Vertex, Vertex> predBck, ArrayList<Vertex> path,
            boolean isReversed) {
        if (lastFwd == lastBck && !predFwd.isEmpty())
            lastFwd = predFwd.get(lastFwd);
        else if (lastBck == from) {
            lastFwd = from;
            lastBck = predBck.get(lastBck);
        }
        // reconstruct forward and backward segments of path
        UnpackPathReversed(from, lastFwd, path, predFwd);
        UnpackPathReversed(to, lastBck, path, predBck);

        // sort vertices by id in ascending order
        Collections.sort(path);

        // append path end
        if (isReversed)
            path.add(from);
        else
            path.add(to);
    }

    private boolean PerformSearches(HashMap<Vertex, Integer> distFwd, HashMap<Vertex, Integer> distBck,
            HashMap<Vertex, Vertex> predFwd, HashMap<Vertex, Vertex> predBck,
            PriorityQueue<Kvp<Vertex>> pqFwd, PriorityQueue<Kvp<Vertex>> pqBck) {
        RelaxEdges(pqFwd.poll().val, pqFwd, distFwd, predFwd, Edge.Direction.forward);

        // stop if forward and backward searches have met
        if (!pqFwd.isEmpty() && distBck.containsKey(pqFwd.peek().val))
            return true;

        RelaxEdges(pqBck.poll().val, pqBck, distBck, predBck, Edge.Direction.backward);

        return false;
    }

    private ArrayList<Vertex> BidirectionalDijkstaMetric(Vertex from, Vertex to) {
        if (from == to)
            return null;

        boolean isReversed = false;
        // maintain low to high id ordering for forward search
        if (from.id > to.id) {
            isReversed = true;
            Vertex tmp = from;
            from = to;
            to = tmp;
        }

        ArrayList<Vertex> path = new ArrayList<>();

        HashMap<Vertex, Integer> distFwd = new HashMap<>();
        HashMap<Vertex, Integer> distBck = new HashMap<>();
        HashMap<Vertex, Vertex> predFwd = new HashMap<>();
        HashMap<Vertex, Vertex> predBck = new HashMap<>();
        distFwd.put(from, 0);
        distBck.put(to, 0);

        PriorityQueue<Kvp<Vertex>> pqFwd = new PriorityQueue<>();
        PriorityQueue<Kvp<Vertex>> pqBck = new PriorityQueue<>();
        pqFwd.add(new Kvp<Vertex>(0, from));
        pqBck.add(new Kvp<Vertex>(0, to));

        while (!pqFwd.isEmpty() || !pqBck.isEmpty()) {
            // stop once forward and backward searches meet
            // searches have met if there's an interstion in their frontiers
            // i.e. if a node visited by one search has been processed by the other
            Vertex lastFwd = pqFwd.isEmpty() ? from : pqFwd.peek().val;
            Vertex lastBck = pqBck.isEmpty() ? to : pqBck.peek().val;
            if (distFwd.containsKey(lastBck) || distBck.containsKey(lastFwd)
                    || PerformSearches(distFwd, distBck, predFwd, predBck, pqFwd, pqBck)) {
                ConstructPathBidirectional(from, lastFwd, lastBck, to, predFwd, predBck, path, isReversed);
                return path;
            }
        }

        throw new IllegalArgumentException(
                "there was no path between given 'from' and 'to' vertices. GraphAdjList contains disjoint components!");
    }

    ArrayList<Vertex> QueryPath(int fromID, int toID) {
        Vertex from = graph.vertices.get(fromID);
        Vertex to = graph.vertices.get(toID);
        return BidirectionalDijkstaMetric(from, to);
    }
};

public class ContractionHierarchies {
    public static void main(String[] args) {
        int numVerts = 10;
        GraphAdjList graph = new GraphAdjList();
        for (int i = 1; i < numVerts; i++) {
            graph.AddEdge(i - 1, i, i);
        }
        Vertex start = graph.vertices.get(0);

        CH chObj = new CH(graph);
        ArrayList<Vertex> path = chObj.QueryPath(0, numVerts - 1);
        System.out.println(start.id);
        for (var v : path)
            System.out.println(v.id);
    }
}
