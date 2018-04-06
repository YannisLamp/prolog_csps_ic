/*
                            Logic Programming
                                Exercise 6
                                                                        */

/*                                tents */

:- lib(ic).

/* 						tents

*/

/* 2 EINAI DENTRA 1 EINAI TENT 0 TIPOTA STO REPRESENTATION */

tents(RowTents, ColumnTents, Trees, Tents) :-
	length(RowTents, RowLen),
	length(ColumnTents, ColLen),
	make_board(RowLen, ColLen, Board),
	insert_trees(Trees, Board, 1, 1),
	
	
	constrain(Liars, Input, Liars, Input, Sum),
	search(Liars, 0, first_fail, indomain_middle, complete, []).

/*						constrain
Puts constrains for each variable in the Solution list.
For each node, if it takes the value 1 (is in the max clique), then all the nodes that
are not connected with it, should have the value 0 (should not be in the max clique)
*/

make_board(0, ColLen, CurrBoard, Board) :-
	length(Row, ColLen),
	Row #:: 0 .. 2,
	invert_list([Row | CurrBoard], Board).

make_board(RowLen, ColLen, CurrBoard, Board) :-
	length(Row, ColLen),
	Row #:: 0 .. 2,
	NewRowLen is RowLen - 1,
	make_board(NewRowLen, ColLen, [Row | CurrBoard], Board).

/* constrain variables in board to be trees */
insert_trees(Trees, [[]], _, _).

insert_trees(Trees, [[] | RestRows], CurrRow, CurrCol) :-
	NewRow is CurrRow + 1,
	insert_trees(Trees, NewRow, 1).

insert_trees(Trees, [[Var | RestCols] | RestRows], CurrRow, CurrCol) :-
	check_if_tree(Trees, CurrRow, CurrCol),
	Var #= 2,
	NewCol is CurrCol + 1,
	insert_trees(Trees, [RestCols | RestRows], CurrRow, NewCol).


	
check_if_tree([Row - Col | RestTrees], CheckRow, CheckCol) :-
	CheckRow =:= Row,
	CheckCol =:= Col.

check_if_tree([_ | RestTrees], CheckRow, CheckCol) :-
	check_if_tree(RestTrees, CheckRow, CheckCol).

constrain([], [], _, _, _).		

constrain([Liar | Rest], [Stmt | Stmts], AllLiars, AllStmts, Sum) :-
	Liar #= 0 => Sum #>= Stmt,
	Liar #= 1 => Sum #< Stmt,
	
	comparison_constr(Liar, Stmt, AllLiars, AllStmts),
	
	constrain(Rest, Stmts, AllLiars, AllStmts, Sum).

	
comparison_constr(_, _, [], []).
	
comparison_constr(Liar, Stmt, [CurrLiar | RestLiars], [CurrStmt | RestStmts]) :-
	Stmt =:= CurrStmt,
	Liar #= CurrLiar,
	comparison_constr(Liar, Stmt, RestLiars, RestStmts).
	
comparison_constr(Liar, Stmt, [CurrLiar | RestLiars], [CurrStmt | RestStmts]) :-
	Stmt > CurrStmt,
	Liar #= 0 => CurrLiar #= 0,
	comparison_constr(Liar, Stmt, RestLiars, RestStmts).
	
comparison_constr(Liar, Stmt, [CurrLiar | RestLiars], [CurrStmt | RestStmts]) :-
	Stmt < CurrStmt,
	Liar #= 1 => CurrLiar #= 1,
	comparison_constr(Liar, Stmt, RestLiars, RestStmts).

/* HELPERS */	
invert_list(List, Inverted) :-
	invert_list_imp(List, [], Inverted).

	
invert_list_imp([], Inverted, Inverted).
	
invert_list_imp([Item | RestList], CurrList, Inverted) :-
	invert_list_imp(RestList, [Item | CurrList], Inverted).
