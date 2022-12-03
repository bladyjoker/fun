:- use_module(library(dcg/basics)).
:- use_module(library(solution_sequences)).
:- set_prolog_flag(double_quotes, chars).

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

challenge_2(Solution) :-
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

