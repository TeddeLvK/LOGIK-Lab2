verify(InputFileName) :-
    see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof).

valid_proof(Prems, Goal, Proof) :-
    check_goal(Goal, Proof),
    check_proof(Prems, Proof, []).

check_goal(Goal, Proof) :-
    last(Proof, [_, Goal, _]).

check_proof(_, [], _).

check_proof(Prems, [Box | Rest], Validated) :-
    is_list(Box),
    Box = [Assump | BoxRest],
    Assump = [_, _, assumption],
    check_proof(Prems, BoxRest, [Assump | Validated]),
    check_proof(Prems, Rest, [Box | Validated]).

check_proof(Prems, [Line | Rest], Validated) :-
    Line = [_, Formula, Rule],
    valid_rule(Rule, Formula, Prems, Validated),
    check_proof(Prems, Rest, [Line | Validated]).

valid_rule(premise, Formula, Prems, _) :-
    member(Formula, Prems).

valid_rule(copy(X), Formula, _, Validated) :-
    member([X, Formula, _], Validated).

valid_rule(andint(X, Y), and(F1, F2), _, Validated) :-
    member([X, F1, _], Validated),
    member([Y, F2, _], Validated).

valid_rule(andel1(X), F, _, Validated) :-
    member([X, and(F, _), _], Validated).

valid_rule(andel2(X), F, _, Validated) :-
    member([X, and(_, F), _], Validated).

valid_rule(orint1(X), or(F, _), _, Validated) :-
    member([X, F, _], Validated).

valid_rule(orint2(X), or(_, F), _, Validated) :-
    member([X, F, _], Validated).

valid_rule(orel(X, Y, U, V, W), F, _, Validated) :-
    member([X, or(F1, F2), _], Validated),
    member(Box1, Validated),
    is_list(Box1),
    Box1 = [[Y, F1, assumption] | _],
    last(Box1, [U, F, _]),
    member(Box2, Validated),
    is_list(Box2),
    Box2 = [[V, F2, assumption] | _],
    last(Box2, [W, F, _]).

valid_rule(impint(X, Y), imp(F1, F2), _, Validated) :-
    member(Box, Validated),
    is_list(Box),
    Box = [[X, F1, assumption] | _],
    last(Box, [Y, F2, _]).

valid_rule(impel(X, Y), F, _, Validated) :-
    member([X, F1, _], Validated),
    member([Y, imp(F1, F), _], Validated).

valid_rule(negint(X, Y), neg(F), _, Validated) :-
    member(Box, Validated),
    is_list(Box),
    Box = [[X, F, assumption] | _],
    last(Box, [Y, cont, _]).

valid_rule(negel(X, Y), cont, _, Validated) :-
    member([X, F, _], Validated),
    member([Y, neg(F), _], Validated).

valid_rule(contel(X), _, _, Validated) :-
    member([X, cont, _], Validated).

valid_rule(negnegint(X), neg(neg(F)), _, Validated) :-
    member([X, F, _], Validated).

valid_rule(negnegel(X), F, _, Validated) :-
    member([X, neg(neg(F)), _], Validated).

valid_rule(mt(X, Y), neg(F1), _, Validated) :-
    member([X, imp(F1, F2), _], Validated),
    member([Y, neg(F2), _], Validated).

valid_rule(pbc(X, Y), F, _, Validated) :-
    member(Box, Validated),
    is_list(Box),
    Box = [[X, neg(F), assumption] | _],
    last(Box, [Y, cont, _]).

valid_rule(lem, or(F, neg(F)), _, _).