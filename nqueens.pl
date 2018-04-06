:- lib(ic).
:- lib(branch_and_bound).

/* Nqueens*/
nqueens(N, Solution, Cost) :-
	length(Solution, N),
	Solution #:: 1..N,
	constrain(Solution, CostList, 1),
	Cost #= max(CostList),
	bb_min(search(Solution, 0, first_fail, indomain_middle, complete, []),
		Cost, bb_options{strategy:restart}).

constrain([], [], _).		
	
constrain([X | Xs], [abs(2*K-X)|CostList], K) :-
	no_attack(X, Xs, 1),
	K1 is K + 1,
	constrain(Xs, CostList, K1).

no_attack(_, [], _).
no_attack(X, [Y|Ys], M) :-
	X #\= Y,
	X #\= Y-M,
	X #\= Y+M,
	M1 is M + 1,
	no_attack(X,Ys,M1).