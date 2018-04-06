/*
                            Logic Programming
                                Exercise 7
                                                                        */
                               /* hcvrp */

:- lib(ic).
:- lib(ic_global).
:- lib(branch_and_bound).

/* 
The Representation used to solve the hcvrp problem is 3 parallel lists of variables
of length equal to the number of vehicles multiplied by the number of clients plus two.
(except for the third list, which, representing the cost of each trip of a vehicle has one
less variable)
The first list is the list containing the solution variables, (used in search) each one of which
represents the destination of a vehicle, and can take the values of 0 up to the number of clients
of the problem.
The second list represents the quantity of products a vehicle carries, when going to the destination
indicated by the variable of the same index in the solution variables list.
The third list represents the cost of the trip a vehicle makes, when it starts from the client
indicated by the variable of the same index in the solution variables list and goes to the destination
indicated by the variable after that. (In the solution variables list)
*/

/*						hcvrp							*/

hcvrp(NC1, NVe, Timeout, Solution, Cost, Time) :-
	/* Get starting time */
    cputime(StrtTime),
	/* Get a number of clients and vehicles
    from data according to input */
    clients(AllClients),
    get_first_N(AllClients, NC1, Clients, _),
    vehicles(AllVehicles),
    get_first_N(AllVehicles, NVe, Vehicles, _),
    /* Create problem variables (problem representation) */
    length(Clients, ClientNum),
	length(Vehicles, VehicleNum),
    VehicleStates is ClientNum + 2,
	SolLen is VehicleNum  * VehicleStates,
	length(SolRoutes, SolLen),
	/* Solution Variables */
    SolRoutes #:: 0 .. ClientNum,
    /* Prune symmetrical solutions */
    constrain_symm(SolRoutes, VehicleStates),
    /* Quantity Variables (the product quantity that each vehicle carries,
    one variable for each destination for each vehicle) */
    length(ProdQuantity, SolLen),
    /* Place constraints for the relation of the solution and quantity variables for
    each vehicle */
    connect_routes_quantity(SolRoutes, ProdQuantity, Clients),
    /* Cost Variables (the cost of the path that each vehicle takes,
    one variable for each destination for each vehicle) */
    CostLen #= SolLen - 1,
	length(RouteCosts, CostLen),
    /* Place constraints for the relation of the solution and cost variables for
    each vehicle */
	connect_roucost(SolRoutes, RouteCosts, Clients),
	/* Constrain Solution Variables */
    place_zero(SolRoutes, -1, ClientNum),
    cons_zero([_ | SolRoutes], 0, ClientNum),
    constrain_occ(SolRoutes, ClientNum),
    /* Constrain Product quantity */
    constrain_quantity(ProdQuantity, VehicleStates, Vehicles),
    /* The Cost Varible is the sum of all the costs of the paths the vehicles take */
	Cost #= sum(RouteCosts), !,
    /* Make the NewTimeout value for bb_min by calculating the current cpu time minus the
    starting time if the input Timeout value is not 0, otherwise return 0 */
	make_timeout(Timeout, StrtTime, NewTimeout), !,
    /* Search for the solution */
	bb_min(search(SolRoutes, 0, most_constrained, indomain_min, complete, []),
		Cost, bb_options{strategy:continue, timeout: NewTimeout}),
	make_solution(SolRoutes, VehicleStates, Solution), !,
    /* Get ending time and calculate how much time has passed for the execution of hcvrp */
	cputime(EndTime),
	Time is round((EndTime - StrtTime) * 100) / 100.
	

/* Prune all symmetrical solutions for each vehicle (If for example the Solution variables
for that vehicle are [0, X1, X2, X3, 0, 0, ...] make sure that X1 > X2) */
constrain_symm(_, VehicleStates) :-
    VehicleStates < 4.

constrain_symm(SolRoutes, VehicleStates) :-
    cons_symm_veh(SolRoutes, VehicleStates).

cons_symm_veh([], _).

cons_symm_veh(SolRoutes, VehicleStates) :-
    get_first_N(SolRoutes, VehicleStates, CurrVehicle, RestVeh),
    OutOfBounds is VehicleStates + 1,
    cons_poss_zero(CurrVehicle, 4, OutOfBounds),
    cons_symm_veh(RestVeh, VehicleStates).

cons_poss_zero(_, OutOfBounds, OutOfBounds).

cons_poss_zero(CurrVehicle, ZeroPos, OutOfBounds) :-
    get_Nth(CurrVehicle, ZeroPos, Zero),
    PreZeroPos is ZeroPos - 1,
    get_Nth(CurrVehicle, PreZeroPos, PreZero),
    OverMiddle is (ZeroPos div 2) + 1,
    make_pairs(2, ZeroPos, OverMiddle, [], Pairs),
    place_cons_zero(CurrVehicle, Pairs, Zero, PreZero),
    NewZeroPos is ZeroPos + 1,
    cons_poss_zero(CurrVehicle, NewZeroPos, OutOfBounds).

make_pairs(OverMiddle, _, OverMiddle, Pairs, Pairs).

make_pairs(Pos, ZeroPos, OverMiddle, TempPairs, Pairs) :-
    SymPos is ZeroPos - Pos + 1,
    NewPos is Pos + 1,
    make_pairs(NewPos, ZeroPos, OverMiddle, [(Pos, SymPos) | TempPairs], Pairs).

place_cons_zero(_, [], _, _).

place_cons_zero(CurrVehicle, [(Pos, SymPos) | RestPairs], Zero, PreZero) :-
    get_Nth(CurrVehicle, Pos, PosVar),
    get_Nth(CurrVehicle, SymPos, SymPosVar),
    (Zero #= 0 and PreZero #\= 0) => PosVar #> SymPosVar,
    place_cons_zero(CurrVehicle, RestPairs, Zero, PreZero).

/* Constrains the occurence of each destination to be 1 in all Solution variables
(Each client can be visited by only one vehicle) */
constrain_occ(_, 0).

constrain_occ(SolRoutes, ClientNum) :-
    occurrences(ClientNum, SolRoutes, 1),
    NewClientNum is ClientNum - 1,
    constrain_occ(SolRoutes, NewClientNum).

/* If a destination of a vehicle is 0, that means that it is back, so make all other
destination (Solution) variables of that vehicle 0 */
cons_zero([_], _, _).

cons_zero([_, _ | Rest], 0, ClientNum) :-
    cons_zero(Rest, ClientNum, ClientNum).

cons_zero([CurrVar, NextVar | Rest], CurrNum, ClientNum) :-
    CurrVar #= 0 => NextVar #= 0,
    NewNum is CurrNum - 1,
    cons_zero([NextVar | Rest], NewNum, ClientNum).

/* For each vehicle the first and last Solution variable is 0 */
place_zero([], -1, _).

place_zero([ZeroVar | Rest], -1, ClientNum) :-
    ZeroVar #= 0,
    place_zero(Rest, ClientNum, ClientNum).

place_zero([ZeroVar | Rest], 0, ClientNum) :-
    ZeroVar #= 0,
    place_zero(Rest, -1, ClientNum).

place_zero([_ | Rest], CurrNum, ClientNum) :-
    NewNum is CurrNum -1,
    place_zero(Rest, NewNum, ClientNum).


/* Constrain quantity (The quantity of items each vehicle carries must not
exceed the input maximum quantity of that vehicle) */
constrain_quantity([], _, []).

constrain_quantity(ProdQuantity, ClientNum, [Vehicle | RestVehicles]) :-
	constrain_quantity_veh(ProdQuantity, ClientNum, Vehicle, RemProdQuantity),
	constrain_quantity(RemProdQuantity, ClientNum, RestVehicles).


constrain_quantity_veh(ProdQuantity, ClientNum, Vehicle, RemProdQuantity) :-
	constrain_quantity_veh_imp(ProdQuantity, ClientNum, Vehicle, [], RemProdQuantity).

constrain_quantity_veh_imp([_ | RestProdQuan], 1, Vehicle, TempVehQuantity, RestProdQuan) :-
	Sum #= sum(TempVehQuantity),
	Sum #>= 0,
	Sum #=< Vehicle.

constrain_quantity_veh_imp([ProdQuan | RestProdQuan], CurrClientNum, Vehicle, 
		TempVehQuantity, RemProdQuantity) :-
	NewClientNum is CurrClientNum - 1,
	constrain_quantity_veh_imp(RestProdQuan, NewClientNum, Vehicle, 
		[ProdQuan | TempVehQuantity], RemProdQuantity).


/* Connect routes with quantity (One Solution variable and one ProductQuantity variable
for each destination of a vehicle) */
connect_routes_quantity(SolRoutes, ProdQuantity, Clients) :-
    make_quanlist(Clients, QuanList),
    connect_routes_quantity_imp(SolRoutes, ProdQuantity, QuanList).

connect_routes_quantity_imp([], [], _).

connect_routes_quantity_imp([Route | RestRoutes], [Quan | RestQuan], QuanList) :-
    Temp #= Route + 1,
    element(Temp, QuanList, Quan),
    connect_routes_quantity_imp(RestRoutes, RestQuan, QuanList).

make_quanlist(Clients, QuanList) :-
    make_quanlist_imp(Clients, [0], QuanList).

make_quanlist_imp([], TempQuanList, QuanList) :-
    invert_list(TempQuanList, QuanList).

make_quanlist_imp([c(Quan, _, _) | Rest], TempQuanList, QuanList) :-
    make_quanlist_imp(Rest, [Quan | TempQuanList], QuanList).


/* Connect routes with costs (One Solution variable and one RouteCost variable
for each destination of a vehicle) */
connect_roucost(SolRoutes, RouteCosts, Clients) :-
    length(Clients, ClientNum),
    ClientsPlusOne is ClientNum + 1,
    make_costlist(Clients, ClientsPlusOne, CostList),
    connect_roucost_imp(SolRoutes, RouteCosts, ClientsPlusOne, CostList).

connect_roucost_imp([_], [], _, _).

connect_roucost_imp([Strt, Dest | RestRoutes], [Cost | RestCosts], ClientsPlusOne, CostList) :-
    Temp #= (Strt * eval(ClientsPlusOne)) + Dest + 1,
    element(Temp, CostList, Cost),
    connect_roucost_imp([Dest | RestRoutes], RestCosts, ClientsPlusOne, CostList).

/* Make list of costs */    
make_costlist(Clients, OutOfBounds, CostList) :-
    make_costlist_imp(0, 0, OutOfBounds, Clients, [], CostList).

make_costlist_imp(OutOfBounds, _, OutOfBounds, _, TempCostList, CostList) :-
    invert_list(TempCostList, CostList).

make_costlist_imp(Strt, OutOfBounds, OutOfBounds, Clients, TempCostList, CostList) :-
    NewStrt is Strt + 1,
	make_costlist_imp(NewStrt, 0, OutOfBounds, Clients, TempCostList, CostList).
        
make_costlist_imp(Strt, Dest, ClientNum, Clients, TempCostList, CostList) :-
    get_distance(Strt, Dest, Clients, Distance),
	PossCost is integer(round(Distance * 1000)),
    NewDest is Dest + 1,
	make_costlist_imp(Strt, NewDest, ClientNum, Clients, 
		[PossCost | TempCostList], CostList).


/* Make Timeout for branch and bound 0 if Timeout_in is 0 */
make_timeout(0, _, 0).

make_timeout(Timeout_in, StrtTime, Output) :-
	cputime(CurrTime),
	TimeSpent is CurrTime - StrtTime,
	Output is Timeout_in - TimeSpent.


/* Convert the list varible solution representation to the wanted output solution format */ 	
make_solution(SolRoutes, VehicleStates, Solution) :-
	make_solution_imp(SolRoutes, VehicleStates, [], Solution).

make_solution_imp([], _, TempSolution, Solution) :-
	invert_list(TempSolution, Solution).

make_solution_imp(SolRoutes, VehicleStates, TempSolution, Solution) :-
	make_solution_veh(SolRoutes, VehicleStates, [], VehSolution, RemSolRoutes),
	make_solution_imp(RemSolRoutes, VehicleStates, [VehSolution | TempSolution], Solution).	


make_solution_veh(SolRoutes, 0, TempVehSolution, VehSolution, SolRoutes) :-
	invert_list(TempVehSolution, VehSolution).

make_solution_veh([0 | Rest], VehicleStates, TempVehSolution, VehSolution, RemSolRoutes) :-
	NewVehicleStates is VehicleStates - 1,
	make_solution_veh(Rest, NewVehicleStates, TempVehSolution,
		VehSolution, RemSolRoutes).

make_solution_veh([Dest | Rest], VehicleStates, TempVehSolution, VehSolution, RemSolRoutes) :-
	NewVehicleStates is VehicleStates - 1,
	make_solution_veh(Rest, NewVehicleStates, [Dest | TempVehSolution],
		VehSolution, RemSolRoutes).


/* Calculate the cartesian distance of two input clients */
get_distance(Same, Same, _, 0).

get_distance(0, Dest, Clients, Distance) :-
	get_client_pos(Dest, Clients, X2, Y2),
	Distance is sqrt(((X2 - 0)^2) +  ((Y2 - 0)^2)).

get_distance(Strt, 0, Clients, Distance) :-
	get_client_pos(Strt, Clients, X1, Y1),
	Distance is sqrt(((0 - X1)^2) +  ((0 - Y1)^2)).

get_distance(Strt, Dest, Clients, Distance) :-
	get_client_pos(Strt, Clients, X1, Y1),
	get_client_pos(Dest, Clients, X2, Y2),
	Distance is sqrt(((X2 - X1)^2) +  ((Y2 - Y1)^2)).


/* Get client position */
get_client_pos(1, [c(_, X, Y) | _], X, Y).

get_client_pos(ClientNum, [_ | RestClients], X, Y) :-
	NewClientNum is ClientNum - 1,
	get_client_pos(NewClientNum, RestClients, X, Y).


/* Get client quantity */	
get_client_quan(1, [c(Quantity, _, _) | _], Quantity).

get_client_quan(ClientNum, [_ | RestClients], Quantity) :-
	NewClientNum is ClientNum - 1,
	get_client_quan(NewClientNum, RestClients, Quantity).
	

/* Helpers */	

/* Get Nth element from list */
get_Nth([Elem | _], 1, Elem).

get_Nth([_ | Rest], N, Elem) :-
    NewN is N - 1,
    get_Nth(Rest, NewN, Elem).


/*  Get first N items of a list and return the remaining list separately */
get_first_N(Input, N, Output, Rem) :-
    get_first_N_imp(Input, N, [], Output, Rem).

get_first_N_imp([], _, TempOut, Output, []) :-
    invert_list(TempOut, Output).

get_first_N_imp(Rem, 0, TempOut, Output, Rem) :-
    invert_list(TempOut, Output).

get_first_N_imp([Item | Rest], N, TempOut, Output, Rem) :-
    NewN is N - 1,
    get_first_N_imp(Rest, NewN, [Item | TempOut], Output, Rem).

	
/* Invert input list */
invert_list(List, Inverted) :-
	invert_list_imp(List, [], Inverted).
	
invert_list_imp([], Inverted, Inverted).
	
invert_list_imp([Item | Rest], TempInverted, Inverted) :-
	invert_list_imp(Rest, [Item | TempInverted], Inverted).


/*                      Data                            */

vehicles([35, 40, 55, 15, 45, 25, 85, 55]).

clients([c(15,  77,  97), c(23, -28,  64), c(14,  77, -39),
         c(13,  32,  33), c(18,  32,   8), c(18, -42,  92),
         c(19,  -8,  -3), c(10,   7,  14), c(18,  82, -17),
         c(20, -48, -13), c(15,  53,  82), c(19,  39, -27),
         c(17, -48, -13), c(12,  53,  82), c(11,  39, -27),
         c(15, -48, -13), c(25,  53,  82), c(14, -39,   7),
         c(22,  17,   8), c(23, -38,  -7)]).


/* Εδώ βρίσκεται commented μια άλλη υλοποίηση του hcvrp, χωρίς τη χρήση των occurrences, 
element όπως είχαμε πει στο μάθημα. Είναι πιο αργή βέβαια, αν θέλετε να της ρίξετε μια ματιά,
κάντε comment όλα τα πιο πάνω και comment out τα από κάτω, ευχαριστώ. */

/*

:- lib(ic).
:- lib(branch_and_bound).

hcvrp(NC1, NVe, Timeout, Solution, Cost, Time) :-
	cputime(StrtTime),
    clients(AllClients),
    get_first_N(AllClients, NC1, Clients, _),
    vehicles(AllVehicles),
    get_first_N(AllVehicles, NVe, Vehicles, _),
    length(Clients, ClientNum),
	length(Vehicles, VehicleNum),
	VehicleStates is ClientNum + 2,
	SolLen is VehicleNum  * VehicleStates,
	length(SolRoutes, SolLen),
	SolRoutes #:: 0 .. ClientNum,
	constrain_symm(SolRoutes, VehicleStates),
	constrain_routes(SolRoutes, ClientNum),
	length(ProdQuantity, SolLen),
    constrain_quantity(ProdQuantity, VehicleStates, Vehicles),
	connect_routes_quantity(SolRoutes, ProdQuantity, Clients),
    CostLen #= SolLen - 1,
	length(RouteCosts, CostLen),
	make_possible_costs(Clients, PossCosts),
	constrain_roucost(SolRoutes, RouteCosts, PossCosts),
	Cost #= sum(RouteCosts), !,
	make_timeout(Timeout, StrtTime, NewTimeout),
	bb_min(search(SolRoutes, 0, most_constrained, indomain_middle, complete, []),
		Cost, bb_options{strategy:continue, timeout: NewTimeout}),
	make_solution(SolRoutes, VehicleStates, Solution),
	cputime(EndTime),
	Time is EndTime - StrtTime.
	

constrain_routes(SolRoutes, ClientNum) :-
    place_zero(SolRoutes, -1, ClientNum),
    different(SolRoutes, []),
    cons_zero([0 | SolRoutes], 0, ClientNum),
    SolSum #= sum(SolRoutes),
    ar_pro_sum(ClientNum, 0, ArProSum),
    SolSum #= eval(ArProSum).


cons_zero([_], _, _).

cons_zero([CurrVar, NextVar | Rest], 0, ClientNum) :-
    cons_zero(Rest, ClientNum, ClientNum).

cons_zero([CurrVar, NextVar | Rest], CurrNum, ClientNum) :-
    CurrVar #= 0 => NextVar #= 0,
    NewNum is CurrNum - 1,
    cons_zero([NextVar | Rest], NewNum, ClientNum).


ar_pro_sum(0, Sum, Sum).

ar_pro_sum(Num, TempSum, Sum) :-
    NewSum is TempSum + Num,
    NewNum is Num - 1,
    ar_pro_sum(NewNum, NewSum, Sum).


different([], _). 

different([SolVar | Rest], PastVars) :-
    different_than(SolVar, PastVars, 1, AndRes),
    SolVar #= 0 or AndRes #= 1,
    different(Rest, [SolVar | PastVars]).


different_than(_, [], AndRes, AndRes).

different_than(Var, [Curr | Rest], TempAndRes, AndRes) :-
    and(TempAndRes, Var #\= Curr, NewAndRes),
    different_than(Var, Rest, NewAndRes, AndRes).


place_zero([], -1, _).

place_zero([ZeroVar | Rest], -1, ClientNum) :-
    ZeroVar #= 0,
    place_zero(Rest, ClientNum, ClientNum).

place_zero([ZeroVar | Rest], 0, ClientNum) :-
    ZeroVar #= 0,
    place_zero(Rest, -1, ClientNum).

place_zero([_ | Rest], CurrNum, ClientNum) :-
    NewNum is CurrNum -1,
    place_zero(Rest, NewNum, ClientNum).


constrain_symm(_, VehicleStates) :-
    VehicleStates < 4.

constrain_symm(SolRoutes, VehicleStates) :-
    cons_symm_veh(SolRoutes, VehicleStates).


cons_symm_veh([], _).

cons_symm_veh(SolRoutes, VehicleStates) :-
    get_first_N(SolRoutes, VehicleStates, CurrVehicle, RestVeh),
    OutOfBounds is VehicleStates + 1,
    cons_poss_zero(CurrVehicle, 4, OutOfBounds),
    cons_symm_veh(RestVeh, VehicleStates).


cons_poss_zero(_, OutOfBounds, OutOfBounds).

cons_poss_zero(CurrVehicle, ZeroPos, OutOfBounds) :-
    get_Nth(CurrVehicle, ZeroPos, Zero),
    PreZeroPos is ZeroPos - 1,
    get_Nth(CurrVehicle, PreZeroPos, PreZero),
    OverMiddle is (ZeroPos div 2) + 1,
    make_pairs(2, ZeroPos, OverMiddle, [], Pairs),
    place_cons_zero(CurrVehicle, Pairs, Zero, PreZero),
    NewZeroPos is ZeroPos + 1,
    cons_poss_zero(CurrVehicle, NewZeroPos, OutOfBounds).


make_pairs(OverMiddle, _, OverMiddle, Pairs, Pairs).

make_pairs(Pos, ZeroPos, OverMiddle, TempPairs, Pairs) :-
    SymPos is ZeroPos - Pos + 1,
    NewPos is Pos + 1,
    make_pairs(NewPos, ZeroPos, OverMiddle, [(Pos, SymPos) | TempPairs], Pairs).


place_cons_zero(_, [], _, _).

place_cons_zero(CurrVehicle, [(Pos, SymPos) | RestPairs], Zero, PreZero) :-
    get_Nth(CurrVehicle, Pos, PosVar),
    get_Nth(CurrVehicle, SymPos, SymPosVar),
    (Zero #= 0 and PreZero #\= 0) => PosVar #> SymPosVar,
    place_cons_zero(CurrVehicle, RestPairs, Zero, PreZero).


constrain_quantity([], _, []).

constrain_quantity(ProdQuantity, ClientNum, [Vehicle | RestVehicles]) :-
	constrain_quantity_veh(ProdQuantity, ClientNum, Vehicle, RemProdQuantity),
	constrain_quantity(RemProdQuantity, ClientNum, RestVehicles).


constrain_quantity_veh(ProdQuantity, ClientNum, Vehicle, RemProdQuantity) :-
	constrain_quantity_veh_imp(ProdQuantity, ClientNum, Vehicle, [], RemProdQuantity).

constrain_quantity_veh_imp([_ | RestProdQuan], 1, Vehicle, TempVehQuantity, RestProdQuan) :-
	Sum #= sum(TempVehQuantity),
	Sum #>= 0,
	Sum #=< Vehicle.

constrain_quantity_veh_imp([ProdQuan | RestProdQuan], CurrClientNum, Vehicle, 
		TempVehQuantity, RemProdQuantity) :-
	NewClientNum is CurrClientNum - 1,
	constrain_quantity_veh_imp(RestProdQuan, NewClientNum, Vehicle, 
		[ProdQuan | TempVehQuantity], RemProdQuantity).


connect_routes_quantity(SolRoutes, ProdQuantity, Clients) :-
    length(Clients, ClientNum),
    connect_routes_quantity_imp(SolRoutes, ProdQuantity, Clients, ClientNum, ClientNum).

connect_routes_quantity_imp([], [], _, _, _).

connect_routes_quantity_imp([Route | RestRoutes], [Quan | RestQuan], Clients, 0, ClientNum) :-
    Route #= 0 => Quan #= 0,
    connect_routes_quantity_imp(RestRoutes, RestQuan, Clients, ClientNum, ClientNum).

connect_routes_quantity_imp([Route | RestRoutes], [Quan | RestQuan], Clients, 
        CurrNum, ClientNum) :-
    get_client_quan(CurrNum, Clients, PossQuan),
    Route #= eval(CurrNum) => Quan #= eval(PossQuan),
    NewNum is CurrNum - 1,
    connect_routes_quantity_imp([Route | RestRoutes], [Quan | RestQuan], Clients, 
        NewNum, ClientNum).


constrain_roucost([_], [], _).

constrain_roucost([Strt, Dest | RestSolRoutes], [RouteCost | RestRouteCosts], PossCosts) :-
	constrain_roucost_veh(Strt, Dest, RouteCost, PossCosts),
	constrain_roucost([Dest | RestSolRoutes], RestRouteCosts, PossCosts).

constrain_roucost_veh(_, _, _, []).

constrain_roucost_veh(Strt, Dest, RouteCost, [(PossStrt, PossDest, PossCost) | RestPossCosts]) :-
	and(Strt #= eval(PossStrt), Dest #= eval(PossDest), AndRes),
	AndRes #= 1 => RouteCost #= eval(PossCost),
	constrain_roucost_veh(Strt, Dest, RouteCost, RestPossCosts).


make_timeout(0, _, 0).

make_timeout(Timeout_in, StrtTime, Output) :-
	cputime(CurrTime),
	TimeSpent is CurrTime - StrtTime,
	Output is Timeout_in - TimeSpent.


make_solution(SolRoutes, VehicleStates, Solution) :-
	make_solution_imp(SolRoutes, VehicleStates, [], Solution).

make_solution_imp([], _, TempSolution, Solution) :-
	invert_list(TempSolution, Solution).

make_solution_imp(SolRoutes, VehicleStates, TempSolution, Solution) :-
	make_solution_veh(SolRoutes, VehicleStates, [], VehSolution, RemSolRoutes),
	make_solution_imp(RemSolRoutes, VehicleStates, [VehSolution | TempSolution], Solution).	


make_solution_veh(SolRoutes, 0, TempVehSolution, VehSolution, SolRoutes) :-
	invert_list(TempVehSolution, VehSolution).

make_solution_veh([0 | Rest], VehicleStates, TempVehSolution, VehSolution, RemSolRoutes) :-
	NewVehicleStates is VehicleStates - 1,
	make_solution_veh(Rest, NewVehicleStates, TempVehSolution,
		VehSolution, RemSolRoutes).

make_solution_veh([Dest | Rest], VehicleStates, TempVehSolution, VehSolution, RemSolRoutes) :-
	NewVehicleStates is VehicleStates - 1,
	make_solution_veh(Rest, NewVehicleStates, [Dest | TempVehSolution],
		VehSolution, RemSolRoutes).


getall_client_quantities(Clients, ClientQuantities) :-
	getall_client_quantities_imp(Clients, [], ClientQuantities).

getall_client_quantities_imp([], ClientQuantities, ClientQuantities).

getall_client_quantities_imp([c(Quantity, _, _) | RestClients], TempQuantities, ClientQuantities) :-
	getall_client_quantities_imp(RestClients, [Quantity | TempQuantities], ClientQuantities).


make_possible_costs(Clients, Costs) :-
	length(Clients, ClientNum),
	make_possible_costs_imp(Clients, ClientNum, ClientNum, ClientNum, [], Costs).

make_possible_costs_imp(_, _, -1, _, Costs, Costs).

make_possible_costs_imp(Clients, ClientNum, Strt, -1, TempCosts, Costs) :-
	NewStrt is Strt - 1,
	make_possible_costs_imp(Clients, ClientNum, NewStrt, ClientNum, TempCosts, Costs).

make_possible_costs_imp(Clients, ClientNum, Strt, Dest, TempCosts, Costs) :-
	NewDest is Dest - 1,
	get_distance(Strt, Dest, Clients, Distance),
	PossCost is integer(round(Distance * 1000)),
	make_possible_costs_imp(Clients, ClientNum, Strt, NewDest, 
		[(Strt, Dest, PossCost) | TempCosts], Costs).


get_distance(Same, Same, _, 0).

get_distance(0, Dest, Clients, Distance) :-
	get_client_pos(Dest, Clients, X2, Y2),
	Distance is sqrt(((X2 - 0)^2) +  ((Y2 - 0)^2)).

get_distance(Strt, 0, Clients, Distance) :-
	get_client_pos(Strt, Clients, X1, Y1),
	Distance is sqrt(((0 - X1)^2) +  ((0 - Y1)^2)).

get_distance(Strt, Dest, Clients, Distance) :-
	get_client_pos(Strt, Clients, X1, Y1),
	get_client_pos(Dest, Clients, X2, Y2),
	Distance is sqrt(((X2 - X1)^2) +  ((Y2 - Y1)^2)).


get_client_pos(1, [c(_, X, Y) | _], X, Y).

get_client_pos(ClientNum, [_ | RestClients], X, Y) :-
	NewClientNum is ClientNum - 1,
	get_client_pos(NewClientNum, RestClients, X, Y).
	
get_client_quan(1, [c(Quantity, _, _) | _], Quantity).

get_client_quan(ClientNum, [_ | RestClients], Quantity) :-
	NewClientNum is ClientNum - 1,
	get_client_quan(NewClientNum, RestClients, Quantity).
	

get_first_N(Input, N, Output, Rem) :-
    get_first_N_imp(Input, N, TempOut, Output, Rem).

get_first_N_imp([], _, TempOut, Output, []) :-
    invert_list(TempOut, Output).

get_first_N_imp(Rem, 0, TempOut, Output, Rem) :-
    invert_list(TempOut, Output).

get_first_N_imp([Item | Rest], N, TempOut, Output, Rem) :-
    NewN is N - 1,
    get_first_N_imp(Rest, NewN, [Item | TempOut], Output, Rem).
	

invert_list(List, Inverted) :-
	invert_list_imp(List, [], Inverted).
	
invert_list_imp([], Inverted, Inverted).
	
invert_list_imp([Item | Rest], TempInverted, Inverted) :-
	invert_list_imp(Rest, [Item | TempInverted], Inverted).
	

vehicles([35, 40, 55, 15, 45, 25, 85, 55]).

clients([c(15,  77,  97), c(23, -28,  64), c(14,  77, -39),
         c(13,  32,  33), c(18,  32,   8), c(18, -42,  92),
         c(19,  -8,  -3), c(10,   7,  14), c(18,  82, -17),
         c(20, -48, -13), c(15,  53,  82), c(19,  39, -27),
         c(17, -48, -13), c(12,  53,  82), c(11,  39, -27),
         c(15, -48, -13), c(25,  53,  82), c(14, -39,   7),
         c(22,  17,   8), c(23, -38,  -7)]).

*/