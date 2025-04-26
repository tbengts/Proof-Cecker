verify(InputFileName) :-
   see(InputFileName),
   read(Prems), read(Goal), read(Proof),
   seen,
   valid_proof(Prems, Goal, Proof).


valid_proof(Prems, Goal, Proof) :-
   valid_goal(Goal, Proof),
   %gå igenom rad för rad och kolla att beviset är korrekt
   valid_lines(Prems, Proof, [], _). %accumulator som fungerar som bokföring för alla lines som gåtts igenom hittills.


%Basfall - när man kommit fram till slutet av beviset så är Proof-listan tom helt enkelt.
valid_lines(_, [], _, _).
%Rekursiv
valid_lines(Prems, [Current_Line|Rest], Checked_Lines, _) :-
   %Kontrollera att Current_line är godkänd enligt den regel som står där.
   check_line(Prems, Current_Line, Checked_Lines, [dummy]),
   %Gör samma för resten av beviset
   valid_lines(Prems, Rest, [Current_Line|Checked_Lines], _).


valid_box_lines(_, [], _, _).
valid_box_lines(Prems, [Current_Line|Rest], Checked_Lines, Box_Lines_Only) :-
   %Kontrollera att Current_line är godkänd enligt den regel som står där.
   check_line(Prems, Current_Line, Checked_Lines, Box_Lines_Only),
   %Gör samma för resten av beviset
   valid_box_lines(Prems, Rest, [Current_Line|Checked_Lines], [Current_Line|Box_Lines_Only]).


valid_goal(Goal, Proof) :-
   last_egen(Proof, LastLine), %LastLine = lista med tre termer
   second_element_equals(LastLine, Goal).
last_egen([R],R).
last_egen([_|T],R) :- last_egen(T,R).
second_element_equals([_,E|_], Element) :- E = Element.


% PREMISS 
check_line(Prems, [_, P, premise], _, _) :- %[Rad, Proposition, regel]
   member(P, Prems).
% ASSUMPTION
check_line(_, [_, _, assumption], _, Box_Lines_Only) :-
   Box_Lines_Only = [].
% COPY
check_line(_, [_, P, copy(X)], Checked_Lines, _) :-
   member([X, P, _], Checked_Lines).
% AND INTRODUCTION 
check_line(_, [_, and(P, Q), andint(X,Y)], Checked_Lines, _) :-
   member([X, P, _], Checked_Lines), 
   member([Y, Q, _], Checked_Lines).
% AND ELIMINATION 1 
check_line(_, [_, P, andel1(X)], Checked_Lines, _) :-
   member([X, and(P, _), _], Checked_Lines).
% AND ELIMINATION 2 
check_line(_, [_, P, andel2(X)], Checked_Lines, _) :-
   member([X, and(_, P), _], Checked_Lines).
% OR INTRODUCTION 1 
check_line(_, [_, or(P,_), orint1(X)], Checked_Lines, _) :-
   member([X, P, _], Checked_Lines).
% OR INTRODUCTION 2 
check_line(_, [_, or(_,Q), orint2(X)], Checked_Lines, _) :-
   member([X, Q, _], Checked_Lines).
% OR ELIMINATION
check_line(_, [_, R, orel(X,Y,U,V,W)], Checked_Lines, _) :-
   member([X, or(P,Q), _], Checked_Lines),
   find_box([Y, P, assumption], [U, R, _], Checked_Lines),
   find_box([V, Q, assumption], [W, R, _], Checked_Lines).
% IMPLICATION INTRODUCTION
check_line(_, [_, imp(P,Q), impint(X,Y)], Checked_Lines, _) :-
   find_box([X, P, assumption], [Y, Q, _], Checked_Lines).
% IMPLICATION ELIMINATION 
check_line(_, [_, Q, impel(X,Y)], Checked_Lines, _) :-
   member([X, P, _], Checked_Lines),
   member([Y, imp(P, Q), _], Checked_Lines).
% NEGATION INTRODUCTION
check_line(_, [_, neg(P), negint(X,Y)], Checked_Lines, _) :-
   find_box([X, P, assumption], [Y, cont, _], Checked_Lines).
% NEGATION ELIMINATION 
check_line(_, [_, cont, negel(X,Y)], Checked_Lines, _) :-
   member([X, P, _], Checked_Lines),
   member([Y, neg(P), _], Checked_Lines).
% CONTRADICTION ELIMINATION 
check_line(_, [_, _, contel(X)], Checked_Lines, _) :-
   member([X, cont, _], Checked_Lines).
% DOUBLE NEGATION INTRODUCTION 
check_line(_, [_, neg(neg(P)), negnegint(X)], Checked_Lines, _) :-
   member([X, P, _], Checked_Lines).
% DOUBLE NEGATION ELIMINATION 
check_line(_, [_, P, negnegel(X)], Checked_Lines, _) :-
   member([X, neg(neg(P)), _], Checked_Lines).
% MODUS TOLLENS 
check_line(_, [_, neg(P), mt(X,Y)], Checked_Lines, _) :-
   member([X, imp(P, Q), _], Checked_Lines),
   member([Y, neg(Q), _], Checked_Lines).   
% PROOF BY CONTRADICTION
check_line(_, [_, P, pbc(X,Y)], Checked_Lines, _) :-
   find_box([X, neg(P), assumption], [Y, cont, _], Checked_Lines).
% LEM 
check_line(_, [_, or(P, neg(P)), lem], _, _).
% BOX
check_line(Prems, Box, Checked_Lines, _) :-
   append([], Checked_Lines, Box_Lines), %så att checked lines inte får massa box-lines på sig när man är klar med denna boxrekursion
   valid_box_lines(Prems, Box, Box_Lines, []).


find_box(First_Row, Last_Row, [Current_Line|Rest]) :-
   nth0(0, Current_Line, First_Row),
   last_egen(Current_Line, Last_Row);
   find_box(First_Row, Last_Row, Rest).
