module Vertex :
  sig
    type t = int (* Really should be Syntax.node, but that causes a dependency loop *)

    val printVertex : t -> string
    val compare : t -> t -> int
  end

module Edge : Map.OrderedType with type t = Vertex.t * Vertex.t

val printEdge : Edge.t -> string

module VertexMap : BatMap.S with type key = Vertex.t

module VertexSet : BatSet.S with type elt = Vertex.t
module VertexSetSet : BatSet.S with type elt = VertexSet.t
module VertexSetMap : BatMap.S with type key = VertexSet.t

module EdgeSet : BatSet.S with type elt = Edge.t

module EdgeMap : BatMap.S with type key = Edge.t

(* VertexMap auxiliaries *)

val vertex_map_to_string : ('a -> string) -> 'a VertexMap.t -> string

val print_vertex_map : ('a -> string) -> 'a VertexMap.t -> unit

(* graph *)

type t

(* raise BadVertex if a vertex v does not belong to a graph's set of vertices, ie: 0..num_vertex-1 *)

exception BadVertex of Vertex.t

val good_vertex : t -> Vertex.t -> unit

val good_graph : t -> unit

(* create a graph with i vertices named 0..i-1 *)

val create : int -> t

(* number of vertices in the graph (named 0..i-1) *)

val num_vertices : t -> int


val fold_vertices : (Vertex.t -> 'a -> 'a) -> Vertex.t -> 'a -> 'a

(** Vertices in the adjacency graph *)
val get_vertices : t -> VertexSet.t

(* add_vertices g n adds n vertices to g *)
val add_vertices : t -> int -> t

(* add_new_in g v creates a new graph with a new node u with an edge u~v *)
val add_new_in : t -> Vertex.t -> t

(* add_new_out g v creates a new graph with a new node u with an edge v~u *)
val add_new_out : t -> Vertex.t -> t

(* edges in the graph *)

val edges : t -> (Vertex.t * Vertex.t) list

(* add_edge g e adds directed edge e to g *)

val add_edge : t -> Edge.t -> t

(* add_edge g l adds all directed edges in l to g *)

val add_edges : t -> Edge.t list -> t

(* add_edge g e adds directed edge e to g *)

val remove_edge : t -> Edge.t -> t

(** Removes multiple edges from the graph. More efficient, than
   multiple calls to remove_edge. Does not raise BadVertex if an edge
   is invalid! *)
val remove_edges : t -> EdgeSet.t -> t

(* neighbors g v returns neighbors of v in g; raise BadVertex if v invalid *)

val neighbors : t -> Vertex.t -> Vertex.t list

(* print graph *)

val print : t -> unit

(* graph to string *)

val to_string : t -> string

(** computes min-cut between s and t and the returns the min-cut and the S and T sets *)
val min_cut : t -> Vertex.t -> Vertex.t -> EdgeSet.t * VertexSet.t * VertexSet.t

module DrawableGraph :
sig

  val graph_dot_file: int -> string -> string
  (** [drawGraph g name] draws the graph g in a file called name.jpg *)
  val drawGraph : t -> string -> unit
end
