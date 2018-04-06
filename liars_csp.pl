/*
                            Logic Programming
                                Exercise 5
                                                                        */

/*                          liars_csp 
						Using fd and fd_global
*/
:- lib(fd).
:- lib(fd_global).


liars_csp(Input, Liars) :-
	length(Input, InLen),
	length(Liars, InLen),
	Liars #:: 0 .. 1,
	sumlist(Liars, Sum),
	constrain(Liars, Input, Sum), !,
	/* labeling is used, not search */
	labeling(Liars).

/*						constrain
Puts constrains for each varible (person) in the Liars list.
Each variable (person), can take one of 2 values (0,1), 
0 if he is not a liar and 1 if he is one.
If a variable (person) takes the value 0 then the sum of the
Liars list (the number of Liars) should be greater than or equal his statement
(and in reverse) Otherwise, the sum should be less than his statement
(and in reverse)
*/

constrain([], [], _).

constrain([Liar | Rest], [Stmt | Stmts], Sum) :-
	Liar #= 0 #<=> Sum #>= Stmt,
	constrain(Rest, Stmts, Sum).

/* 
Labeling implementation (Commented out)
(Not needed as it is implemented in global_fd!)  

labeling([]).
	
labeling(L) :-
	deleteff(Var, L, Rest),
	indomain(Var),
	labeling(Rest).
*/
	
/* 						given genrand code */
genrand(N, List) :-
	length(List, N),
	make_list(N, List).
	
make_list(_, []).
make_list(N, [X|List]) :-
	random(R),
	X is R mod (N+1),
	make_list(N, List).

/*					
				LIARS_CSP IMPLEMENTATION USING IC
	COMMENTED OUT, BECAUSE BY USING FD LARGER INPUTS CAN BE PROCESSED 
	
	
:- lib(ic).


liars_csp(Input, Liars) :-
	length(Input, InLen),
	length(Liars, InLen),
	Liars #:: 0 .. 1,
	Sum #= sum(Liars),
	constrain(Liars, Input, Sum), !,
	labeling(Liars).

constrain([], [], _).

constrain([Liar | Rest], [Stmt | Stmts], Sum) :-
	Liar #= 0 => Sum #>= Stmt,
	Liar #= 1 => Sum #< Stmt,
	constrain(Rest, Stmts, Sum).

*/
