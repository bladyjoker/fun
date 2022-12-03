:- use_module(library(dcg/basics)).
:- use_module(library(solution_sequences)).
:- set_prolog_flag(double_quotes, codes).

input_1_elf([]) --> blank.

input_1_elf([C|Cs]) -->
    number(C),
    blank,
    input_1_elf(Cs).

input_1([]) --> eos.

input_1([elf(Cs)|Rest]) -->
    input_1_elf(Cs),
    input_1(Rest).

sum_by_elf(Input, Elf, Calories) :-
    member(elf(Elf), Input),
    aggregate_all(sum(Calorie), (member(Calorie, Elf)), Calories).

challenge_1(Solution) :-
    phrase_from_file(input_1(Input), "input_1"),
    aggregate_all(
        max(Calories),
        (sum_by_elf(Input, _, Calories)),
        Solution
    ).

challenge_1b(Solution) :-
    phrase_from_file(input_1(Input), "input_1"),
    aggregate_all(
        sum(Calories),
        (limit(3,
               order_by(
                   [desc(Calories)],
                   sum_by_elf(Input, _, Calories)
               )
              )
         ),
        Solution
    ).

input_2([]) --> eos.

input_2([G|Games]) -->
    input_2_game(G),
    blank,
    input_2(Games).

input_2_game(Them-Me) -->
    input_2_them(Them),
    blank,
    input_2_me(Me).

input_2_them(rock) --> "A".
input_2_them(paper) --> "B".
input_2_them(scissors) --> "C".

input_2_me(rock) --> "X".
input_2_me(paper) --> "Y".
input_2_me(scissors) --> "Z".

score_outcome(X-X, 3).
score_outcome(scissors-rock, 6).
score_outcome(paper-rock, 0).
score_outcome(rock-paper, 6).
score_outcome(scissors-paper, 0).
score_outcome(paper-scissors, 6).
score_outcome(rock-scissors, 0).

score_move(rock, 1).
score_move(paper, 2).
score_move(scissors, 3).

score_game(Them-Me, Score) :-
    score_outcome(Them-Me, OScore),
    score_move(Me, MScore),
    Score is OScore + MScore.

challenge_2(Total) :-
    phrase_from_file(input_2(Input), "input_2"),
    aggregate_all(sum(S), (member(G, Input), score_game(G, S)), Total).

input_2_correctify(rock, lose).
input_2_correctify(paper, draw).
input_2_correctify(scissors, win).

choose_strategy(X-draw, X).
choose_strategy(rock-lose, scissors).
choose_strategy(rock-win, paper).
choose_strategy(paper-lose, rock).
choose_strategy(paper-win, scissors).
choose_strategy(scissors-lose, paper).
choose_strategy(scissors-win, rock).

challenge_2b(Total) :-
    phrase_from_file(input_2(Input), "input_2"),
    aggregate_all(
        sum(S),
        (
            member(Them-Me, Input),
            input_2_correctify(Me, Me_),
            choose_strategy(Them-Me_, MyMove),
            score_game(Them-MyMove, S)
        ),
        Total
    ).

input_3([]) --> eos.
input_3([R|Rs]) --> input_3_rucksack(R), input_3(Rs).
input_3_rucksack([]) --> blank.
input_3_rucksack([C|Cs]) --> [C], {char_type(C, alpha)}, input_3_rucksack(Cs).

priority(C, I_) :-
    char_code('A', IA),
    char_code('Z', IZ),
    IA_ is 27,
    IZ_ is IA_ + (IZ-IA),
    between(IA_,IZ_,I_),
    I is I_ + (IA - IA_),
    char_code(C, I).

priority(C, I_) :-
    char_code('a', IA),
    char_code('z', IZ),
    IA_ is 1,
    IZ_ is IA_ + (IZ-IA),
    between(IA_,IZ_,I_),
    I is I_ + (IA - IA_),
    char_code(C, I).

challenge_3(Total) :-
    phrase_from_file(input_3(Input), "input_3"),
    aggregate_all(
        sum(S),
        (
            member(Rucksack, Input),
            append(X,Y,Rucksack), length(X,N), length(Y,N),
            list_to_set(X,X_),
            list_to_set(Y,Y_),
            intersection(X_,Y_,Is),
            member(I,Is),
            char_code(C, I),
            priority(C, S)
        ),
        Total).

challenge_3b(Total) :-
    phrase_from_file(input_3b(Input), "input_3"),
    aggregate_all(
        sum(S),
        (
            member(R1-R2-R3, Input),
            list_to_set(R1,R1_),
            list_to_set(R2,R2_),
            list_to_set(R3,R3_),
            intersection(R1_,R2_,R_),
            intersection(R_,R3_,R),
            member(I, R),
            char_code(C, I),
            priority(C, S)
        ),
        Total).

input_3b([]) --> eos.
input_3b([R1-R2-R3|Rs]) -->
    input_3_rucksack(R1),
    input_3_rucksack(R2),
    input_3_rucksack(R3),
    input_3b(Rs).
