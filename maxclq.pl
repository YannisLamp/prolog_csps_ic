/*
                            Logic Programming
                                Exercise 4
                                                                        */
:- lib(ic).
:- lib(branch_and_bound).

/* 						maxclq 
Maxclq searches for a solution to the max graph clique problem
The Solution is a list of N elements where N is the number of nodes in the graph,
so each element represents a node of the graph.
Each element has a domain of {0,1} where 0 means that the element it represents is not in 
the max clique, and 1 means that it is.
At the end, that solution is converted to the wanted Clique output from the examples (translate_sol) 
*/

maxclq(N, D, Clique, Size) :-
	create_graph(N, D, Graph),
	length(Solution, N), !,
	Solution #:: 0 .. 1,
	constrain(Solution, Graph, 1),
	Cost #= N - sum(Solution),
	bb_min(search(Solution, 0, first_fail, indomain_middle, complete, []),
		Cost, bb_options{strategy:continue}),
	translate_sol(Solution, 1, [], Clique),
	length(Clique, Size).

/*						constrain
Puts constrains for each variable in the Solution list.
For each node, if it takes the value 1 (is in the max clique), then all the nodes that
are not connected with it, should have the value 0 (should not be in the max clique)
*/

constrain([_], _, _).		

constrain([Node | Nodes], Graph, CurrNum) :-
	make_neighborlist(CurrNum, Graph, [], NeighborList),
	NewNum is CurrNum + 1,
	constrain_not_neighbors(Node, Nodes, NewNum, NeighborList),
	constrain(Nodes, Graph, NewNum).

/*						make_neighborlist	
Examines only A in the graph list [A - B | RestOfGraph]. 
(finds only neighbors whose names (values) are greater than that of A)
That is because in all the given graphs, A < B.
*/

make_neighborlist(_, [], NeighborList, NeighborList).

make_neighborlist(CurrNum, [CurrNum - B | T], CurrList, NeighborList) :-
	append(CurrList, [B], NewList),
	make_neighborlist(CurrNum, T, NewList, NeighborList).

make_neighborlist(CurrNum, [A - _ | T], CurrList, NeighborList) :-
	A > CurrNum ->
	append(CurrList, [], NeighborList) ;
	make_neighborlist(CurrNum, T, CurrList, NeighborList).
	

/*						constrain_not_neighbors 
Constrains with #\= only greater nodes in name (for 2 we constrain 3,4...) 
That happens because the constraints for the nodes with lesser name values have 
already been made.
*/

constrain_not_neighbors(_, [], _, []).
 
constrain_not_neighbors(Node, [_ | Nodes], CurrNum, [CurrNum | Neighbors]) :-
	NewNum is CurrNum + 1,
	constrain_not_neighbors(Node, Nodes, NewNum, Neighbors).

constrain_not_neighbors(Node, [SecNode | Nodes], CurrNum, Neighbors) :-
	Node #= 1 => SecNode #= 0,
	NewNum is CurrNum + 1,
	constrain_not_neighbors(Node, Nodes, NewNum, Neighbors).

/*						translate_sol
Translates the solution to the max clique problem to the wanted Clique answer 
*/

translate_sol([], _, Clique, Clique).

translate_sol([1 | Nodes], CurrNum, CurrClique, Clique) :-
	append(CurrClique, [CurrNum], NewClique),
	NewNum is CurrNum + 1,
	translate_sol(Nodes, NewNum, NewClique, Clique).
	
translate_sol([0 | Nodes], CurrNum, CurrClique, Clique) :-
	NewNum is CurrNum + 1,
	translate_sol(Nodes, NewNum, CurrClique, Clique).

/* 						given create_graph code */

create_graph(NNodes, Density, Graph) :-
   cr_gr(1, 2, NNodes, Density, [], Graph).

cr_gr(NNodes, _, NNodes, _, Graph, Graph).
cr_gr(N1, N2, NNodes, Density, SoFarGraph, Graph) :-
   N1 < NNodes,
   N2 > NNodes,
   NN1 is N1 + 1,
   NN2 is NN1 + 1,
   cr_gr(NN1, NN2, NNodes, Density, SoFarGraph, Graph).
cr_gr(N1, N2, NNodes, Density, SoFarGraph, Graph) :-
   N1 < NNodes,
   N2 =< NNodes,
   rand(1, 100, Rand),
   (Rand =< Density ->
      append(SoFarGraph, [N1 - N2], NewSoFarGraph) ;
      NewSoFarGraph = SoFarGraph),
   NN2 is N2 + 1,
   cr_gr(N1, NN2, NNodes, Density, NewSoFarGraph, Graph).

rand(N1, N2, R) :-
   random(R1),
   R is R1 mod (N2 - N1 + 1) + N1.
