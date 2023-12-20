% License: GPLv3
% (C) David Strohmaier
% Based on the research work by Bradley Franks (https://philpapers.org/rec/FRASGA)

:- use_module(library(reif)).
:- use_module(library(lists)).
:- use_module(library(dif)).
:- use_module(library(ordsets)).
:- op(500,xfy,:).

%%%%%% Below are the lexical entries, which encode the core word senses

lex(lion,
    [rav(central:[
             rav(organic:val(true),true),
             rav(animate:val(true),true),
             rav(genus:val(lion),true),
             rav(biological_essence:(lion),true)
         ],
         true),
     rav(diagnostic:[
             rav(legs:val(4),true),
             rav(tail:val(1),true),
             rav(texture:val(soft),true),
             rav(colour:val(tawny),true)
         ],
         true)
    ]).

lex(gun,
    [rav(central:[
             rav(fires:val(bullets),true),
             rav(made_of:val(metal),true),
             rav(mechanism:val(explosion),true),
             rav(function:(explosion),true)
         ],
         true),
     rav(diagnostic:[
             rav(trigger:val(true),true),
             rav(size:val(portable),true),
             rav(barrel:val(true),true),
             rav(handel:val(true),true),
             rav(colour:val(grey),true)
         ],
         true)
    ]).


lex(stone,
    [rav(central:[
             rav(organic:val(false),true),
             rav(animate:val(false),true),
             rav(solid:val(true),true)
         ],
         true),
     rav(diagnostic:[
             rav(hard:val(true),true),
             rav(texture:val(rough),true),
             rav(weight:val(heavy),true),
             rav(colour:val(grey),true)
         ],
         true)
    ]).


lex(wild,
    [rav(central:[
             rav(organic:val(true),true),
             rav(animate:val(true),true),
             rav(domesticated:val(false),true)
         ],
         true),
     rav(diagnostic:[
             rav(location:val(wilderness),true)
         ],
        true)
    ]).

test_lex(fake_gun,
         [rav(central:[
                  rav(fires:val(bullets),false),
                  rav(made_of:val(metal),false),
                  rav(mechanism:val(explosion),false),
                  rav(function:(explosion),false)
              ],
              true),
          rav(diagnostic:[
                  rav(trigger:val(true),true),
                  rav(size:val(portable),true),
                  rav(barrel:val(true),true),
                  rav(handel:val(true),true),
                  rav(colour:val(grey),true)
              ],
              true)
         ]).

test_lex(wild_lion,
    [rav(central:[
             rav(organic:val(true),true),
             rav(animate:val(true),true),
             rav(genus:val(lion),true),
             rav(biological_essence:(lion),true),
             rav(domesticated:val(false),true)
         ],
         true),
     rav(diagnostic:[
             rav(legs:val(4),true),
             rav(tail:val(1),true),
             rav(texture:val(soft),true),
             rav(colour:val(tawny),true),
             rav(location:val(wilderness),true)
         ],
         true)
    ]).


test_lex(stone_lion,
         [rav(central:[
                  rav(organic:val(false),true),
                  rav(animate:val(false),true),
                  rav(solid:val(true),true),
                  rav(genus:val(lion),false),
                  rav(biological_essence:(lion),false)
              ],
              true),
          rav(diagnostic:[
                  rav(hard:val(true),true),
                  rav(texture:val(rough),true),
                  rav(weight:val(heavy),true),
                  rav(colour:val(grey),true),
                  rav(legs:val(4),true),
                  rav(tail:val(1),true)
              ],
              true)
         ]).


%%%% Below is the main code implementing the operations


% when we use the lexical entries directly, then the unification could be destructive.
% Ungrounded variables could be grounded once and then not unified again.
% To avoid this issue in a principled manner, we use a
retrieved_lex(Word,AVS) :-
    lex(Word, ORIGINAL_AVS),
    copy_term(ORIGINAL_AVS,AVS).
% copy term to avoid destruction of original data


% non predicate as present in reif library (but not exported there)
non(true,false).
non(false,true).


% Some privatives, such as "fake", invert the central AVS in the mtc_r operation
inverted_avs([],[]).
inverted_avs([rav(A:V,B)|T],[rav(A:V,INVERTED_B)|INVERTED_T]) :-
    non(B,INVERTED_B),
    inverted_avs(T,INVERTED_T).


% predicate encoding the mtc_r relation. Selects central AVS and return it inverted
mtc_r([rav(central:AVS,true),rav(diagnostic:AVS_DIAGNOSTIC,true)|_],
      [rav(central:INVERTED_AVS,true),rav(diagnostic:AVS_DIAGNOSTIC,true)]) :- inverted_avs(AVS,INVERTED_AVS).


% filtering reified attribute value pairs (RAV) into those with matching
% and those without matching attribute name.
filter_attributes(F1,rav(F2:V,B),split(Inc-I,Exc-E),split(Inc-NI,Exc-NE)) :-
    if_(
        F1=F2,
        (I=[rav(F1:V,B)|NI],E=NE),
        (E=[rav(F2:V,B)|NE],I=NI)
    ).
% destructive unification of feature names (F1, F2),
% The destructive predicate is acceptable as long as lexical entries are copied using retrieved_lex.

and(A, B, T) :-
    if_(A=true,
        T=B,
        T=false).

% avs_unify unifies to attribute value structures (AVS).
% The first AVS (AVS1) serves as a default structure.
% If there is a disagreement between AVS1 and AVS2 on a reified Attribute-Value (RAV),
% then the RAV of the AVS1 is used.
% In the priority case, the reified truth value of the unification (SUCCESS) will be false.
avs_unify(AVS1,AVS2,AVSU,SUCCESS) :-
    foldl(rav_unify,AVS1,state(AVS2,X-X,true),state(RestAVS2,AVSU-RestAVS2,SUCCESS)).

% rav_unify encodes the unification relation between two reified Attribute-Value pairs
rav_unify(rav(F1:V1,B1),state(AVS2,AVSU-A,SUCCESS),state(ReducedAVS2,AVSU-NA,NewSUCCESS)) :-
    foldl(filter_attributes(F1),AVS2,split(X-X,Y-Y),split(Matched-[],ReducedAVS2-[])),
    if_(
        Matched=[],
        (A=[rav(F1:V1,B1)|NA],SUCCESS=NewSUCCESS),
        (Matched=[rav(F1:V2,B2)],val_unify(V1,V2,B1,B2,NewV,NewB,ValSUCCESS),
         A=[rav(F1:NewV,NewB)|NA],and(ValSUCCESS,SUCCESS,NewSUCCESS))
    ).
% We are using difference-lists to make the appending faster.


reif_list_to_ord_set(LS,OS,B) :-
    list_to_ord_set(LS,OS2),
    if_(
        OS=OS2,
        B=true,
        B=false
    ).


% Assumption is that Value1 and Value2 are different boolean truth values.
% In this case they are only unifiable if the reified boolean values for the RAVs also differ.
mixed_bool_unify(Value1,Value2,B1,B2,SUCCESS) :-
    list_to_ord_set([Value1,Value2],[false,true]),
    if_(
        reif_list_to_ord_set([B1,B2],[false,true]),
        (SUCCESS=true),
        (SUCCESS=false)
    ).

val_unify([H|T],[H2|T2],B,B,UAVS,B,SUCCESS) :- avs_unify([H|T],[H2|T2],UAVS,SUCCESS).
% At the moment, we are not allowing empty lists as values.
val_unify(val(Value1),val(Value2),B1,B2,val(Value1),NewB,SUCCESS) :-
    if_(
        reif_list_to_ord_set([Value1,Value2],[false,true]),
        mixed_bool_unify(Value1,Value2,B1,B2,SUCCESS),
        (=(Value1,Value2,ValSUCCESS),
         =(B1,B2,BoolSUCCESS),
         and(ValSUCCESS,BoolSUCCESS,SUCCESS),
         B1=NewB)
    ).
% destructive unification of values, acceptable as long as lexical entries are copied using retrieved_lex.
% Use of Value1 as default.

%%%% Below are tests for checking correctness

% test0 checks that we correctly apply the privative "fake" to "gun".
test0 :- retrieved_lex(gun,AVS1), mtc_r(AVS1,AVS_INV), test_lex(fake_gun,AVS_INV).

% test1 checks that we correctly unify with an empty list as AVS
test1 :- retrieved_lex(lion,AVS1), avs_unify(AVS1,[],AVS1,true).

% test2 checks
% a) that the unification can capture the non-privative case of "wild lion"
% b) that the unification in this case is non-destructive (using dif for this purpose)
test2 :- retrieved_lex(lion,AVS1), retrieved_lex(wild,AVS2), avs_unify(AVS1,AVS2,AVSU,true), test_lex(wild_lion,AVSU), dif(AVS1,AVSU), dif(AVS2,AVSU), dif(AVS1,AVS2).

% test3 checks the more complicated case of "stone lion".
% Two operations have to be used mtc_r and unification with priority
test3 :- retrieved_lex(lion,AVS1), retrieved_lex(stone,AVS2), mtc_r(AVS1,AVS_INV), avs_unify(AVS2,AVS_INV,AVSU,false), test_lex(stone_lion,AVSU), dif(AVS1,AVSU), dif(AVS2,AVSU), dif(AVS1,AVS2).
