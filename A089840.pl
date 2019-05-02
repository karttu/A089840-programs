%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                    %%
%% http://www.research.att.com/~njas/sequences/A089840p.txt           %%
%%                                                                    %%
%% A set of Prolog-definitions that illustrate how the first rows     %%
%% of A089840 are produced.                                           %%
%%                                                                    %%
%% Written by Antti Karttunen, 2003, http://www.iki.fi/kartturi/      %%
%%                                                                    %%
%% Last edited May 22, 2007 by AK.                                    %%
%%                                                                    %%
%% This works (at least) with GNU prolog version 1.2.16               %%
%% (Copyright (C) 1999-2002 Daniel Diaz)                              %%
%%  see: http://www.gnu.org/software/prolog                           %%
%%                                                                    %%
%% Load as:                                                           %%
%% consult('./A089840p.txt').                                         %%
%% then "execute" with:                                               %%
%% findall([G|S],signatperm(G,64,S),GMs_with_their_sigperms).         %%
%% or: findall([G|S],signatperm(G,196,S),GMs_with_their_sigperms).    %%
%%                                                                    %%
%% For the C-implementation of these same automorphisms, see:         %%
%% from http://www.research.att.com/~njas/sequences/a089839.c.txt     %%
%%                                                                    %%
%% For the Scheme implementations, see:                               %%
%% http://www.iki.fi/kartturi/matikka/Nekomorphisms/gatomorf.htm      %%
%%                                                                    %%
%% If you have any suggestions or questions, you can mail them to me  %%
%% to my address <My firstname>.<My surname>@gmail.com                %%
%%                                                                    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%
% Definitions:
%
%  A "non-recursive Catalan automorphism" is such an automorphism of
%  unlabeled rooted plane binary trees (see A014486) whose behaviour
%  is always, no matter how large the tree is, determined by the
%  information obtained from the finite set of nodes situated at
%  constant, finite distances from the root.
%  Note that the only information the nodes contain (being unlabeled)
%  is whether they are leaves (terminal nodes) or whether they are
%  "internal" nodes, branching to further subtrees to the left and/or
%  to the right.

%
%  Clause-representation of a non-recursive Catalan automorphism is a
%  sequence of zero or more "clauses" followed by a default clause.
%
%  Viewed combinatorially, a clause of n opening conses consists of
%  a pair of rooted plane binary trees (both with n internal nodes),
%  of which the other one is unlabeled, and the other one's terminal
%  nodes are labeled. The sequence A089835(n) = (A000108(n)^2)*(n+1)!
%  gives the number of such clauses.
%

%  In this Prolog-implementation a "clause" is literally a Prolog clause
%  (a.k.a. "rule") whose body is a conjunctive query of cons-clauses,
%  defined below.


% The two-way "cons" is a clause which either "cleaves" open an existing
% cons cell (i.e. a branching node of the binary tree with its left and
% right sides), or constructs a new one, from the given left and right
% subtrees:

cons(CAR,CDR,[CAR|CDR]).

% That is: if the first and the second argument are instantiated,
% constructs a new cons cell (to be placed to the third,
% uninstantiated argument), with CAR as its left subtree,
% and CDR as its right subtree.
% If the first and the second argument are uninstantiated,
% but the third one is instantiated, then obtain its
% left side (CAR) and its right side (CDR), and place
% them to the first and second arguments.


% Examples of simple non-recursive automorphisms follow.


% From each (after the trivial identity permutation gma001477)
% we list its
%  defining CLAUSE-sequence structure
%  from http://www.research.att.com/~njas/sequences/a089839.c.txt
%
%  its effects on Lisp/Scheme dotted-pairs,
%
%  and on the rooted plane binary trees illustrated with simple ASCII art,
%
%  and its defining Prolog-clause definition, with deliberate use of red cuts.
%  The "opening" conses are given above the % -- comment line,
%  and the "closing" ones below it.
%
% Each Prolog-definition ends with the "catch-all" default clause
% of the form gmaxxxxx(X,X). which will fix all those S-expressions
% which were not handled by any previous clauses (i.e. those above it).


% The four numbers for each non-default clause in clause sequences
% refer to the size of the tree (number of internal nodes opened (closed)),
% the local rank of the source tree,
% the local rank of the destination tree,
% the rank of the permutation used in the labels of destination tree.

% The ranks of source and destination trees employ the standard
% lexicographic ranking order as employed in the OEIS entry A014486.

% For permutations we use the unranking/ranking system as illustrated
% by the entry A060118 in OEIS, which works like this:
% (permute-a060118 (vector 'a 'b 'c) 3 0)  -->  #(a b c)
% (permute-a060118 (vector 'a 'b 'c) 3 1)  -->  #(b a c)
% (permute-a060118 (vector 'a 'b 'c) 3 2)  -->  #(a c b)
% (permute-a060118 (vector 'a 'b 'c) 3 3)  -->  #(b c a)
% (permute-a060118 (vector 'a 'b 'c) 3 4)  -->  #(c b a)
% (permute-a060118 (vector 'a 'b 'c) 3 5)  -->  #(c a b)
% See also: http://www.iki.fi/~kartturi/matikka/Nekomorphisms/gatogenp.scm

%  For each non-recursive Catalan automorphism there exists
%  the unique minimal clause-representation, which from all
%  the possible clause-representations of that automorphism
%  is the "least" clause sequence, where the total order
%  of clause sequences is defined by the following rules:
%
%   A) All the clause sequences have an associated integer
%      (see the macro CLAUSESEQ_binexp in a089839.c.txt), whose
%      binary expansion's run lengths determine the number of
%      clauses and their sizes.
%      Of two clause sequences with differing values for this
%      integer, the one with smaller value, is also "less than"
%      in this context. The run lenghs of the least significant
%      end of the binary expansion correspond to the sizes of
%      the most significant clauses, and vice versa.
%
%      E.g. from 103, whose binary expansion is 1100111
%      we get clauses of sizes 3, 2 and 2, from the most
%      significant to the least signicant clause.
%      Similarly, from 124, whose binary expansion is 1111100,
%      we get two clauses, the more significant, with
%      binary trees of 2 internal nodes, and the less
%      significant, with binary trees of 5 internal nodes.
%
%   B) The "most distinguishing clause" of a clause sequence
%      in relation to the other clause sequence of the same
%      size, is the most significant clause, which differs from
%      the corresponding clause in the other clause sequence.
%      Here the most significant clause means the clause which is
%      executed first, the least significant being the one which
%      is applied last, before the default identity clause,
%      in case none of the previous, "more significant" clauses
%      matched. If there is no such dinstinguishing clause,
%      then the two clause sequences are identical.
%
%   C) If the above conditions cannot determine the relation
%      of two clause sequences (in this total order)
%      then the "lesser" clause sequence is the one where the
%      source binary tree used in the most distinguishing clause
%      is nearer to the beginning of the sequence A014486.
%      (I.e. lexicographically less as determined by the
%       established ordering of unlabeled rooted plane binary trees).
%
%   D) If the above conditions cannot determine the relation
%      of two clause sequences in this total order
%      then the "lesser" clause sequence is the one where the
%      destination binary tree of the most distinguishing clause
%      is lexicographically "less", as determined by the sequence A014486.
%
%   E) If the above conditions cannot determine the relation
%      of two clause sequences in this total order
%      then the "lesser" clause sequence is the one where the
%      the permutation used in the destination binary tree
%      of the most distinguishing clause is the least one as
%      ordered by the sequence A060118.
%      (Note that this differs from the established "lexicographic"
%       orderings of permutations, like used in A030299 and A055089).
%

% The Prolog-definitions here try to give the minimal clause-representations,
% with non-minimal representations indicated with the letter 'b'
% (such as gma089864b for the automorphism *A089864.)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                    %%
%% One non-recursive automorphism with 0 non-default clauses          %%
%% and 0 opening (closing) conses.                                    %%
%%                                                                    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA001477[] = { CLAUSESEQ_begin(0,0) }; /* A089840[0] */

gma001477(X,X). %% Only the default clause, the Identity which fixes everything.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                    %%
%% One non-recursive automorphism with 1 non-default clause of        %%
%% 1 opening (closing) cons:                                          %%
%%                                                                    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA069770[] = { CLAUSESEQ_begin(1,1), { 1, 0, 0, 1 } };/*A089840[1] */
% (a . b) --> (b . a)
%
% A   B   -->   B   A
%  \ /           \ /
%   X0            Y0

gma069770(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma069770(X,X). %% The default clause, fix S-exprs (here just []) the above clause could not handle.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                    %%
%% 10 non-recursive automorphisms with one non-default clause of      %%
%% two opening (closing) conses:                                      %%
%%                                                                    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA072796[] = { CLAUSESEQ_begin(3,1), { 2, 0, 0, 1 } };/* A089840[2] */
% (a . (b . c)) --> (b . (a . c))
%
%   B   C         A   C
%    \ /           \ /
% A   X1    --> B   Y1
%  \ /           \ /
%   X0            Y0

gma072796(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,C,Y1),
  cons(B,Y1,Y0),
  !.

gma072796(X,X). %% Fix [] and S-exprs of length 1.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA089850[] = { CLAUSESEQ_begin(3,1), { 2, 0, 0, 2 } };/*A089840[3] */
% (a . (b . c)) --> (a . (c . b))
%
%   B   C         C   B
%    \ /           \ /
% A   X1    --> A   Y1
%  \ /           \ /
%   X0            Y0


gma089850(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(C,B,Y1),
  cons(A,Y1,Y0),
  !.

gma089850(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% CLAUSE gmA089851[] = { CLAUSESEQ_begin(3,1), { 2, 0, 0, 3 } };/* A089840[4] */
%
%   B   C         C   A
%    \ /           \ /
% A   X1    --> B   Y1
%  \ /           \ /
%   X0            Y0


gma089851(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(C,A,Y1),
  cons(B,Y1,Y0),
  !.

gma089851(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% CLAUSE gmA089852[] = { CLAUSESEQ_begin(3,1), { 2, 0, 0, 4 } };/* A089840[5] */
%
%   B   C         B   A
%    \ /           \ /
% A   X1    --> C   Y1
%  \ /           \ /
%   X0            Y0


gma089852(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(B,A,Y1),
  cons(C,Y1,Y0),
  !.

gma089852(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% CLAUSE gmA089853[] = { CLAUSESEQ_begin(3,1), { 2, 0, 0, 5 } };/* A089840[6] */
% (a . (b . c)) --> (c . (a . b))
%
%   B   C         A   B
%    \ /           \ /
% A   X1    --> C   Y1
%  \ /           \ /
%   X0            Y0


gma089853(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,B,Y1),
  cons(C,Y1,Y0),
  !.

gma089853(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA089854[] = { CLAUSESEQ_begin(3,1), { 2, 1, 1, 1 } };/* A089840[7] */
% ((a . b) . c) --> ((b . a) . c)
%
%
%  A   B         B   A
%   \ /           \ /
%    X1  C   -->   Y1  C
%     \ /           \ /
%      X0            Y0

gma089854(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(B,A,Y1),
  cons(Y1,C,Y0),
  !.

gma089854(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% CLAUSE gmA072797[] = { CLAUSESEQ_begin(3,1), { 2, 1, 1, 2 } };/* A089840[8] */
% ((a . b) . c) --> ((a . c) . b)
%
%
%  A   B         A   C
%   \ /           \ /
%    X1  C   -->   Y1  B
%     \ /           \ /
%      X0            Y0

gma072797(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(A,C,Y1),
  cons(Y1,B,Y0),
  !.

gma072797(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA089855[] = { CLAUSESEQ_begin(3,1), { 2, 1, 1, 3 } };/* A089840[9] */
% ((a . b) . c) --> ((b . c) . a)
%
%
%  A   B         B   C
%   \ /           \ /
%    X1  C   -->   Y1  A
%     \ /           \ /
%      X0            Y0

gma089855(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(B,C,Y1),
  cons(Y1,A,Y0),
  !.

gma089855(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA089856[] = { CLAUSESEQ_begin(3,1), { 2, 1, 1, 4 } };/* A089840[10] */
% ((a . b) . c) --> ((c . b) . a)
%
%  A   B         C   B
%   \ /           \ /
%    X1  C   -->   Y1  A
%     \ /           \ /
%      X0            Y0

gma089856(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(C,B,Y1),
  cons(Y1,A,Y0),
  !.

gma089856(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA089857[] = { CLAUSESEQ_begin(3,1), { 2, 1, 1, 5 } };/* A089840[11] */
% ((a . b) . c) --> ((c . a) . b)
%
%  A   B         C   A
%   \ /           \ /
%    X1  C   -->   Y1  B
%     \ /           \ /
%      X0            Y0

gma089857(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(C,A,Y1),
  cons(Y1,B,Y0),
  !.

gma089857(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                    %%
%% 10 Non-recursive automorphisms with two non-default clauses        %%
%% of 2 & 1 opening (closing) conses.                                 %%
%%                                                                    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% CLAUSE gmA074679[] = { CLAUSESEQ_begin(4,2), { 2, 0, 1, 0,}, { 1,0, 0, 1 } }; /* A089840[12] */
% (a . (b . c)) --> ((a . b) . c)
% (a . ()) --> (() . a)
%
%   B   C     A   B
%    \ /       \ /
% A   X1   -->  Y1  C        A  []    -->    []  A
%  \ /           \ /          \ /             \ /
%   X0            Y0           X0              Y0

gma074679(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,B,Y1),
  cons(Y1,C,Y0),
  !.

gma074679(X0,Y0) :-
  cons(A,B,X0), % B = [] by above clause.
% --
  cons(B,A,Y0),
  !.

gma074679(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA089858[] = { CLAUSESEQ_begin(4,2), { 2, 0, 1, 1,}, { 1, 0,0, 1 } }; /* A089840[13] */
% (a . (b . c)) --> ((b . a) . c)
% (a . ()) --> (() . a)
%
%   B   C     B   A
%    \ /       \ /
% A   X1   -->  Y1  C        A  []    -->    []  A
%  \ /           \ /          \ /             \ /
%   X0            Y0           X0              Y0



gma089858(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(B,A,Y1),
  cons(Y1,C,Y0),
  !.

gma089858(X0,Y0) :-
  cons(A,B,X0), % B = [] by above clause.
% --
  cons(B,A,Y0),
  !.

gma089858(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA073269[] = { CLAUSESEQ_begin(4,2), { 2, 0, 1, 2,}, { 1, 0,0, 1 } }; /* A089840[14] */
% (a . (b . c)) --> ((a . c) . b)
% (a . ()) --> (() . a)
%
%   B   C     A   C
%    \ /       \ /
% A   X1   -->  Y1  B        A  []    -->    []  A
%  \ /           \ /          \ /             \ /
%   X0            Y0           X0              Y0


gma073269(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,C,Y1),
  cons(Y1,B,Y0),
  !.

gma073269(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma073269(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA089859[] = { CLAUSESEQ_begin(4,2), { 2, 0, 1, 4,}, { 1, 0,0, 1 } }; /* A089840[15] */
% (a . (b . c)) --> ((c . b) . a)
% (a . ()) --> (() . a)
%
%   B   C     C   B
%    \ /       \ /
% A   X1   -->  Y1  A        A  []    -->    []  A
%  \ /           \ /          \ /             \ /
%   X0            Y0           X0              Y0


gma089859(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(C,B,Y1),
  cons(Y1,A,Y0),
  !.

gma089859(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma089859(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA089860[] = { CLAUSESEQ_begin(4,2), { 2, 0, 1, 5,}, { 1, 0,0, 1 } }; /* A089840[16] */
% (a . (b . c)) --> ((c . a) . b)
% (a . ()) --> (() . a)
%
%   B   C     C   A
%    \ /       \ /
% A   X1   -->  Y1  B        A  []    -->    []  A
%  \ /           \ /          \ /             \ /
%   X0            Y0           X0              Y0


gma089860(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(C,A,Y1),
  cons(Y1,B,Y0),
  !.

gma089860(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma089860(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA074680[] = { CLAUSESEQ_begin(4,2), { 2, 1, 0, 0 }, { 1, 0,0, 1 } }; /* A089840[17] */
% ((a . b) . c) --> (a . (b . c))
% (() . b) --> (b . ())

%
% A   B             B   C
%  \ /               \ /
%   X1  C  -->    A   Y1       []  B   -->     B  []
%    \ /           \ /          \ /             \ /
%     X0            Y0           X0              Y0

gma074680(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(B,C,Y1),
  cons(A,Y1,Y0),
  !.

gma074680(X0,Y0) :-
  cons(A,B,X0), % A = [] by above clause.
% --
  cons(B,A,Y0),
  !.

gma074680(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA089861[] = { CLAUSESEQ_begin(4,2), { 2, 1, 0, 1,}, { 1, 0,0, 1 } }; /* A089840[18] */

% ((a . b) . c) --> (b . (a . c))
% (() . b) --> (b . ())
%
% A   B             A   C
%  \ /               \ /
%   X1  C  -->    B   Y1       []  B   -->     B  []
%    \ /           \ /          \ /             \ /
%     X0            Y0           X0              Y0


gma089861(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(A,C,Y1),
  cons(B,Y1,Y0),
  !.

gma089861(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma089861(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA073270[] = { CLAUSESEQ_begin(4,2), { 2, 1, 0, 2,}, { 1, 0,0, 1 } }; /* A089840[19] */

% ((a . b) . c) --> (a . (c . b))
% (() . b) --> (b . ())
%
% A   B             C   B
%  \ /               \ /
%   X1  C  -->    A   Y1       []  B   -->     B  []
%    \ /           \ /          \ /             \ /
%     X0            Y0           X0              Y0


gma073270(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(C,B,Y1),
  cons(A,Y1,Y0),
  !.

gma073270(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma073270(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA089862[] = { CLAUSESEQ_begin(4,2), { 2, 1, 0, 3,}, { 1, 0,0, 1 } }; /* A089840[20] */
% ((a . b) . c) --> (b . (c . a))
% (() . b) --> (b . ())
%
% A   B             C   A
%  \ /               \ /
%   X1  C  -->    B   Y1       []  B   -->     B  []
%    \ /           \ /          \ /             \ /
%     X0            Y0           X0              Y0


gma089862(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(C,A,Y1),
  cons(B,Y1,Y0),
  !.

gma089862(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma089862(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA089863[] = { CLAUSESEQ_begin(4,2), { 2, 1, 0, 4,}, { 1, 0, 0, 1 } }; /* A089840[21] */
% ((a . b) . c) --> (c . (b . a))
% (() . b) --> (b . ())
%
% A   B             B   A
%  \ /               \ /
%   X1  C  -->    C   Y1       []  B   -->     B  []
%    \ /           \ /          \ /             \ /
%     X0            Y0           X0              Y0


gma089863(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(B,A,Y1),
  cons(C,Y1,Y0),
  !.

gma089863(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma089863(X,X).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Note that the { CLAUSESEQ_begin(4,2), { 2, 0, 1, 3,}, { 1, 0,0, 1 } };
% is not used here, as it would result a duplicate of gma069770:
%
% (a . (b . c)) --> ((b . c) . a)
% (a . ()) --> (() . a)
%
%   B   C     B   C
%    \ /       \ /
% A   X1   -->  Y1  A        A  []    -->    []  A
%  \ /           \ /          \ /             \ /
%   X0            Y0           X0              Y0

% Similarly for { CLAUSESEQ_begin(4,2), { 2, 1, 0, 5,}, { 1, 0, 0, 1 } };
% ((a . b) . c) --> (c . (a . b))
% (() . b) --> (b . ())
%
% A   B             A   B
%  \ /               \ /
%   X1  C  -->    C   Y1       []  B   -->     B  []
%    \ /           \ /          \ /             \ /
%     X0            Y0           X0              Y0
%
% which also is a duplicate of a simple swap (gma069770).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                    %%
%% Five examples out of 139 non-recursive automorphisms with          %%
%% two non-default clauses with total 4 opening (closing) conses.     %%
%%                                                                    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% CLAUSE gmA129611[] = { CLAUSESEQ_begin(8,2), { 3, 1, 4, 10,}, { 1, 0, 0, 1 } }; /* A089840[169] */
% (a . ((b . c) . d)) --> (((c . b) . d) . a)
% (a . b)             --> (b . a)   [b implied () or (() . X)]

%      B   C     C   B
%       \ /       \ /
%        X2  D     Y2  D
%         \ /       \ /
%      A   X1  -->   Y1  A      A   B    -->   B   A
%       \ /           \ /        \ /            \ /
%        X0            Y0         X0             Y0
%
%

gma129611(X0,Y0) :-
  cons(A,X1,X0),
  cons(X2,D,X1),
  cons(B,C,X2),
% --
  cons(C,B,Y2),
  cons(Y2,D,Y1),
  cons(Y1,A,Y0),
  !.

gma129611(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma129611(X,X).


%% CLAUSE gmA129612[] = { CLAUSESEQ_begin(8,2), { 3, 4, 1, 22,}, { 1, 0, 0, 1 } }; /* A089840[251] */
% (((a . b) . c) . d) --> (d . ((b . a) . c))
% (a . b)             --> (b . a)   [a implied () or (() . X)]

% This involution effects the following transformation:
%  A   B             B   A
%   \ /               \ /
%    X2  C            Y2   C
%     \ /               \ /
%      X1  D   -->   D  Y1         A   B   -->  B   A
%       \ /           \ /           \ /          \ /
%        X0            Y0            X0           Y0
%

gma129612(X0,Y0) :-
  cons(X1,D,X0),
  cons(X2,C,X1),
  cons(A,B,X2),
% --
  cons(B,A,Y2),
  cons(Y2,C,Y1),
  cons(D,Y1,Y0),
  !.

gma129612(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma129612(X,X).



%% CLAUSE gmA123503[] = { CLAUSESEQ_begin(12,2), { 2, 0, 0, 1,}, { 2, 1, 1, 1 } }; /* A089840[253] */
% (a . (b . c)) --> (b . (a . c))
% ((a . b) . c) --> ((b . a) . c)
%
%   B   C         A   C    A   B           B   A
%    \ /           \ /      \ /             \ /
% A   X1   -->  B   Y1       X1 []    -->    Y1 []
%  \ /           \ /          \ /             \ /
%   X0            Y0           X0              Y0

gma123503(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,C,Y1),
  cons(B,Y1,Y0),
  !.

gma123503(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(B,A,Y1),
  cons(Y1,C,Y0),
  !.

gma123503(X,X).


%% CLAUSE gmA123499[] = { CLAUSESEQ_begin(12,2), { 2, 0, 1, 0,}, { 2, 1, 0, 4 } }; /* A089840[258] */
% (a . (b . c)) --> ((a . b) . c)
% ((a . b) . c) --> (c . (b . a))
%
%   B   C     A   B        A   B               B   A
%    \ /       \ /          \ /                 \ /
% A   X1   -->  Y1  C        X1 []    -->    []  Y1
%  \ /           \ /          \ /             \ /
%   X0            Y0           X0              Y0

gma123499(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,B,Y1),
  cons(Y1,C,Y0),
  !.

gma123499(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(B,A,Y1),
  cons(C,Y1,Y0),
  !.

gma123499(X,X).


%% CLAUSE gmA123500[] = { CLAUSESEQ_begin(12,2), { 2, 1, 0, 0,}, { 2, 0, 1, 4 } }; /* A089840[264] */
% ((a . b) . c) --> (a . (b . c))
% (a . (b . c)) --> ((c . b) . a)
%
% A   B             B   C        B   C       C   B
%  \ /               \ /          \ /         \ /
%   X1  C  -->    A   Y1       []  X1   -->    Y1  []
%    \ /           \ /          \ /             \ /
%     X0            Y0           X0              Y0

gma123500(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(B,C,Y1),
  cons(A,Y1,Y0),
  !.

gma123500(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(C,B,Y1),
  cons(Y1,A,Y0),
  !.

gma123500(X,X).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                    %%
%% Seven examples out of 2570 non-recursive automorphisms with        %%
%% two non-default clauses of total 5 opening (closing) conses.       %%
%%                                                                    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% All the examples have 3 opening (closing) conses in the first
%% clause, and 2 opening (closing) conses in the second.


% CLAUSE gmA129607[] = { CLAUSESEQ_begin(24,2), { 3, 0, 0, 0,}, { 2, 0, 0, 1 } }; /* A089840[3608] */
% (a . (b . (c . d))) --> (a . (b . (c . d)))
% (a . (b . c))       --> (b . (a . c))   [c implied ()]
%
%       C   D         C   D
%        \ /           \ /
%     B   X2        B   Y2      B   C       A   C
%      \ /           \ /         \ /         \ /
%   A   X1    --> A   Y1      A   X1  --> B   Y1  (C is [])
%    \ /           \ /         \ /         \ /
%     X0            Y0          X0          Y0

 
gma129607(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,X2,X1),
  cons(C,D,X2),
% --
  cons(C,D,Y2),
  cons(B,Y2,Y1),
  cons(A,Y1,Y0),
  !.


% Above clause implies that C=[].
gma129607(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,C,Y1),
  cons(B,Y1,Y0),
  !.

gma129607(X,X). %% Fix the rest, i.e. S-exprs of the form (a . ()) and ()

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA129605[] = { CLAUSESEQ_begin(24,2), { 3, 0, 0, 3,}, { 2, 0, 0, 1 } }; /* A089840[3613] */
% (a . (b . (c . d))) --> (b . (c . (a . d)))
% (a . (b . c))       --> (b . (a . c))   [c implied ()]
%
%       C   D         A   D
%        \ /           \ /
%     B   X2        C   Y2      B   C       A   C
%      \ /           \ /         \ /         \ /
%   A   X1    --> B   Y1      A   X1  --> B   Y1  (C is [])
%    \ /           \ /         \ /         \ /
%     X0            Y0          X0          Y0

 
gma129605(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,X2,X1),
  cons(C,D,X2),
% --
  cons(A,D,Y2),
  cons(C,Y2,Y1),
  cons(B,Y1,Y0),
  !.


% Above clause implies that C=[].
gma129605(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,C,Y1),
  cons(B,Y1,Y0),
  !.

gma129605(X,X). %% Fix the rest, i.e. S-exprs of the form (a . ()) and ()

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA129606[] = { CLAUSESEQ_begin(24,2), { 3, 0, 0, 5,}, { 2, 0, 0, 1 } }; /* A089840[3617] */
% (a . (b . (c . d))) --> (c . (a . (b . d)))
% (a . (b . c))       --> (b . (a . c))   [c implied ()]
%
%       C   D         B   D
%        \ /           \ /
%     B   X2        A   Y2      B   C       A   C
%      \ /           \ /         \ /         \ /
%   A   X1    --> C   Y1      A   X1  --> B   Y1  (C is [])
%    \ /           \ /         \ /         \ /
%     X0            Y0          X0          Y0

 
gma129606(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,X2,X1),
  cons(C,D,X2),
% --
  cons(B,D,Y2),
  cons(A,Y2,Y1),
  cons(C,Y1,Y0),
  !.


% Above clause implies that C=[].
gma129606(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,C,Y1),
  cons(B,Y1,Y0),
  !.

gma129606(X,X). %% Fix the rest, i.e. S-exprs of the form (a . ()) and ()

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



% CLAUSE gmA082353[] = { CLAUSESEQ_begin(24,2), { 3, 2, 0, 0 }, { 2, 0, 0, 3 } }; /* A089840[3886] */
% ((a . b) . (c . d)) --> (a . (b . (c . d)))
% (a . (b . c))       --> (b . (c . a))   [a implied ()]
%
%                     C   D
%                      \ /
% A  B C  D         B   Y2      B   C       C   A
%  \ / \ /           \ /         \ /         \ /
%   X1  X2    --> A   Y1      A   X1  --> B   Y1  (A is [])
%    \ /           \ /         \ /         \ /
%     X0            Y0          X0          Y0


gma082353(X0,Y0) :-
  cons(X1,X2,X0),
  cons(A,B,X1),
  cons(C,D,X2),
% --
  cons(C,D,Y2), %% Note: Y2 is equal to X2.
  cons(B,Y2,Y1),
  cons(A,Y1,Y0),
  !.


% Above clause implies that A=[].
gma082353(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(C,A,Y1),
  cons(B,Y1,Y0),
  !.

gma082353(X,X). %% Fix the rest, i.e. S-exprs of the form (a . ()) and ()


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA082354[] = { CLAUSESEQ_begin(24,2), { 3, 0, 2, 0 }, { 2, 0, 0, 5 } }; /* A089840[3702] */
% (a . (b . (c . d))) --> ((a . b) . (c . d))
% (a . (b . c))       --> (c . (a . b))   [c implied ()]
%
%         C   D
%          \ /
%       B   X2    A  B C  D      B   C        A   B
%        \ /       \ / \ /        \ /          \ /
%     A   X1  -->   Y1  Y2     A   X1  -->  C   Y1
%      \ /           \ /        \ /          \ /
%       X0            Y0         X0           Y0


gma082354(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,X2,X1),
  cons(C,D,X2),
% --
  cons(A,B,Y1),
  cons(C,D,Y2), % Note that Y2 is equal to X2.
  cons(Y1,Y2,Y0),
  !.

gma082354(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1), % C implied [] by above clause.
% --
  cons(A,B,Y1),
  cons(C,Y1,Y0),
  !.

gma082354(X,X). %% Fix the rest, i.e. S-exprs of the form (a . ()) and ()

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA082351[] = { CLAUSESEQ_begin(24,2), { 3, 2, 4, 0 }, { 2, 1, 1, 5 } }; /* A089840[4069] */
% ((a . b) . (c . d)) --> (((a . b) . c) . d)
% ((a . b) . c)       --> ((c . a) . b)   [c implied ()]
%
%             A   B
%              \ /
% A  B C  D     Y2   C      A   B       []  A
%  \ / \ /       \ /         \ /         \ /
%   X1  X2    --> Y1  D       X1  []  --> Y1  B
%    \ /           \ /         \ /         \ /
%     X0            Y0          X0          Y0


gma082351(X0,Y0) :-
  cons(X1,X2,X0),
  cons(A,B,X1),
  cons(C,D,X2),
% --
  cons(A,B,Y2), %% Note: Y2 is equal to X1.
  cons(Y2,C,Y1),
  cons(Y1,D,Y0),
  !.


% Above clause implies that C=[].
gma082351(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(C,A,Y1),
  cons(Y1,B,Y0),
  !.

gma082351(X,X). %% Fix the rest, i.e. S-exprs of the form (() . b) and ()

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% CLAUSE gmA082352[] = { CLAUSESEQ_begin(24,2), { 3, 4, 2, 0 }, { 2, 1, 1, 3 } }; /* A089840[4253] */
% (((a . b) . c) . d) --> ((a . b) . (c . d))
% ((a . b) . c)       --> ((b . c) . a)   [a implied ()]
%
% A   B
%  \ /
%   X2  C         A  B C  D  []  B        B   C
%    \ /           \ / \ /    \ /          \ /
%     X1  D   -->   Y1  Y2     X1  C   -->  Y1  []
%      \ /           \ /        \ /          \ /
%       X0            Y0         X0           Y0


gma082352(X0,Y0) :-
  cons(X1,D,X0),
  cons(X2,C,X1),
  cons(A,B,X2),
% --
  cons(A,B,Y1), % Note that Y1 is equal to X2.
  cons(C,D,Y2),
  cons(Y1,Y2,Y0),
  !.


gma082352(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1), % A implied [] by above clause.
% --
  cons(B,C,Y1),
  cons(Y1,A,Y0),
  !.

gma082352(X,X). %% Fix the rest, i.e. S-exprs of the form (() . b) and ()




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                    %%
%% Four examples out of 904 non-recursive automorphisms with          %%
%% three non-default clauses of total 6 opening (closing) conses.     %%
%%                                                                    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% CLAUSE gmA129609[] = { CLAUSESEQ_begin(39,3), { 3, 1, 2, 0,}, { 2, 0, 1, 2 }, { 1, 0, 0, 1 } }; /* A089840[65167] */

% (a . ((b . c) . d)) --> ((a . b) . (c . d))
% (a . (b . c))       --> ((a . c) . b) [b implied ()]
% (a . b)             --> (b . a)       [b implied ()]

%      B   C
%       \ /
%        X2  D     A  B C   D      B   C    A   C
%         \ /       \ / \  /        \ /      \ /
%      A   X1  -->   Y1  Y2      A   X1  -->  Y1  B       A   B   -->   B   A
%       \ /           \ /         \ /          \ /         \ /           \ /
%        X0            Y0          X0           Y0          X0            Y0
%
%

gma129609(X0,Y0) :-
  cons(A,X1,X0),
  cons(X2,D,X1),
  cons(B,C,X2),
% --
  cons(A,B,Y1),
  cons(C,D,Y2),
  cons(Y1,Y2,Y0),
  !.


gma129609(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,C,Y1),
  cons(Y1,B,Y0),
  !.

gma129609(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma129609(X,X).


%% CLAUSE gmA129610[] = { CLAUSESEQ_begin(39,3), { 3, 2, 1, 0,}, { 2, 1, 0, 2 }, { 1, 0, 0, 1 } }; /* A089840[65352] */

% ((a . b) . (c . d)) --> (a . ((b . c) . d))
% ((a . b) . c)       --> (a . (c . b))   [c implied ()]
% (a . b)             --> (b . a)         [a implied ()]
%
%                 B   C
%                  \ /
% A  B C  D         Y2  D   A   B           C   B
%  \ / \ /           \ /     \ /             \ /
%   X1  X2    --> A   Y1      X1  C -->   A   Y1       A   B       B   A
%    \ /           \ /         \ /         \ /          \ /   -->   \ /
%     X0            Y0          X0          Y0           X0          Y0

gma129610(X0,Y0) :-
  cons(X1,X2,X0),
  cons(A,B,X1),
  cons(C,D,X2),
% --
  cons(B,C,Y2),
  cons(Y2,D,Y1),
  cons(A,Y1,Y0),
  !.

gma129610(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(C,B,Y1),
  cons(A,Y1,Y0),
  !.

gma129610(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma129610(X,X).


% CLAUSE gmA123495[] = { CLAUSESEQ_begin(39,3), { 3, 2, 4, 16 }, { 2, 0, 1, 0 }, { 1, 0, 0, 1 } }; /* A089840[65518] */
% ((a . b) . (c . d)) --> (((c . d) . a) . b)
% (a . (b . c))       --> ((a . b) . c)   [a implied ()]
% (a . b)             --> (b . a)         [b implied ()]
%
%             C   D
%              \ /
% A  B C  D     Y2  A           B   C   []  B
%  \ / \ /       \ /             \ /     \ /
%   X1  X2    --> Y1  B       []  X1  --> Y1  C       A  []       []  A
%    \ /           \ /         \ /         \ /         \ /   -->   \ /
%     X0            Y0          X0          Y0          X0          Y0


gma123495(X0,Y0) :-
  cons(X1,X2,X0),
  cons(A,B,X1),
  cons(C,D,X2),
% --
  cons(C,D,Y2), %% Note: Y2 is equal to X2.
  cons(Y2,A,Y1),
  cons(Y1,B,Y0),
  !.


% Above clause implies that A=[].
gma123495(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,B,Y1),
  cons(Y1,C,Y0),
  !.


gma123495(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma123495(X,X). %% Fix the ().

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA123496[] = { CLAUSESEQ_begin(39,3), { 3, 4, 2, 16 }, { 2, 1, 0, 0 }, { 1, 0, 0, 1 } }; /* A089840[65796] */
% (((a . b) . c) . d) --> ((c . d) . (a . b))
% ((a . b) . c)       --> (a . (b . c))   [a implied ()]
% (a . b)             --> (b . a)         [a implied ()]
%
% A   B
%  \ /
%   X2  C         C  D A  B  []  B            B   C
%    \ /           \ / \ /    \ /              \ /
%     X1  D   -->   Y1  Y2     X1  C   -->  []  Y1    []  B       B  []
%      \ /           \ /        \ /          \ /       \ /   -->   \ /
%       X0            Y0         X0           Y0        X0          Y0


gma123496(X0,Y0) :-
  cons(X1,D,X0),
  cons(X2,C,X1),
  cons(A,B,X2),
% --
  cons(C,D,Y1),
  cons(A,B,Y2), % Note that Y2 is equal to X2.
  cons(Y1,Y2,Y0),
  !.


gma123496(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1), % A implied [] by above clause.
% --
  cons(B,C,Y1),
  cons(A,Y1,Y0),
  !.


gma123496(X0,Y0) :-
  cons(A,B,X0),
% --
  cons(B,A,Y0),
  !.

gma123496(X,X). %% Fix the ().



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                    %%
%% One example out of 47878 non-recursive automorphisms with          %%
%% two non-default clauses of total 6 opening (closing) conses.       %%
%%                                                                    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% CLAUSE gmA123492[] = { CLAUSESEQ_begin(56,2), { 3, 1, 4, 9 }, { 3, 4, 1, 23 } }; /* A089840[79361] */
% (a . ((b . c) . d)) --> (((b . c) . d) . a)
% (((a . b) . c) . d) --> (d . ((a . b) . c))   [d implied () or (() . X)]

% This involution effects the following transformation:
%      B   C     B   C
%       \ /       \ /
%        X2  D     Y2  D
%         \ /       \ /
%      A   X1  -->   Y1  A
%       \ /           \ /  
%        X0            Y0  
%
%  A   B             A   B
%   \ /               \ /
%    X2  C            Y2   C
%     \ /               \ /
%      X1  D   -->   D  Y1 
%       \ /           \ /  
%        X0            Y0  
%
% In Scheme this can be defined just as:
% (define (*A123492! s)
%   (cond ((null? s) s)
%         ((and (pair? (cdr s)) (pair? (cadr s))) (*A069770! s))
%         ((and (pair? (car s)) (pair? (caar s))) (*A069770! s))
%   )
%   s
% )

gma123492(X0,Y0) :-
  cons(A,X1,X0),
  cons(X2,D,X1),
  cons(B,C,X2),
% --
  cons(B,C,Y2),
  cons(Y2,D,Y1),
  cons(Y1,A,Y0),
  !.

% Implies either D=[] or D=[[]|...]
gma123492(X0,Y0) :-
  cons(X1,D,X0),
  cons(X2,C,X1),
  cons(A,B,X2),
% --
  cons(A,B,Y2),
  cons(Y2,C,Y1),
  cons(D,Y1,Y0),
  !.

gma123492(X,X). %% Fix the rest.


% Another version, as the clauses can be specified in either order:
%
% CLAUSE gmA123492b[] = { CLAUSESEQ_begin(56,2), { 3, 4, 1, 23 }, { 3, 1, 4, 9 } };
% (((a . b) . c) . d) --> (d . ((a . b) . c))
% (a . ((b . c) . d)) --> (((b . c) . d) . a)   [a implied () or (() . X)]

% This involution effects the following transformation:
%  A   B             A   B
%   \ /               \ /
%    X2  C            Y2   C
%     \ /               \ /
%      X1  D   -->   D  Y1 
%       \ /           \ /  
%        X0            Y0  
%
%      B   C     B   C
%       \ /       \ /
%        X2  D     Y2  D
%         \ /       \ /
%      A   X1  -->   Y1  A
%       \ /           \ /  
%        X0            Y0  
%
% In Scheme this can be defined just as:
% (define (*A123492v2! s)
%   (cond ((null? s) s)
%         ((and (pair? (car s)) (pair? (caar s))) (*A069770! s))
%         ((and (pair? (cdr s)) (pair? (cadr s))) (*A069770! s))
%   )
%   s
% )

gma123492b(X0,Y0) :-
  cons(X1,D,X0),
  cons(X2,C,X1),
  cons(A,B,X2),
% --
  cons(A,B,Y2),
  cons(Y2,C,Y1),
  cons(D,Y1,Y0),
  !.

% Implies either A=[] or A=[[]|...]
gma123492b(X0,Y0) :-
  cons(A,X1,X0),
  cons(X2,D,X1),
  cons(B,C,X2),
% --
  cons(B,C,Y2),
  cons(Y2,D,Y1),
  cons(Y1,A,Y0),
  !.

gma123492b(X,X). %% Fix the rest.



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                    %%
%% Six examples out of 20972 non-recursive automorphisms with         %%
%% three non-default clauses of total 7 opening (closing) conses.     %%
%%                                                                    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA073281[] = { CLAUSESEQ_begin(103,3), { 3, 1, 1, 7,}, { 2, 0, 1, 2 }, { 2, 1, 0, 2 } }; /* A089840[1654023] */
%
%     B   C         A   D
%      \ /           \ /
%       X2  D         Y2  C      B   C    A   C     A   B           C   B
%        \ /           \ /        \ /      \ /       \ /             \ /
%     A   X1  -->   B   Y1     A   X1  -->  Y1  B     X1  C  -->  A   Y1
%      \ /           \ /        \ /          \ /       \ /         \ /
%       X0            Y0         X0           Y0        X0          Y0

% Note that if we come to the second clause, then B is implied (),
% and if we come to the third clause, then C is implied ().

gma073281(X0,Y0) :-
  cons(A,X1,X0),
  cons(X2,D,X1),
  cons(B,C,X2),
% --
  cons(A,D,Y2),
  cons(Y2,C,Y1),
  cons(B,Y1,Y0),
  !.

gma073281(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,C,Y1),
  cons(Y1,B,Y0),
  !.

gma073281(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(C,B,Y1),
  cons(A,Y1,Y0),
  !.

gma073281(X,X). %% Fix the rest.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% The "square" of A089859/A089863.
% CLAUSE gmA089864[] = { CLAUSESEQ_begin(103,3), { 3, 2, 2, 7,}, { 2, 0, 0, 2 }, { 2, 1, 1, 1 } }; /* A089840[1654694] */
% ((a . b) . (c . d)) --> ((b . a) . (d . c))
% (a . (b . c))       --> (a . (c . b))   [a implied ()]
% ((a . b) . c)       --> ((b . a) . c)   [c implied ()]
%
% This involution effects the following transformation:
%
%  A  B C  D     B  A D  C       B   C       C   B       A   B        B   A
%   \ / \ /       \ / \ /         \ /         \ /         \ /          \ /
%    X1  X2   -->  Y1  Y2      A   X1  --> A   Y1          X1  C  -->   Y1  C  
%     \ /           \ /         \ /         \ /             \ /          \ /
%      X0            Y0          X0          Y0              X0           Y0
%

% In Scheme this can be defined just as:
% (define (gma089864! s)
%   (cond ((pair? s)
%            (if (pair? (car s)) (swap! (car s)))
%            (if (pair? (cdr s)) (swap! (cdr s)))
%         )
%   )
%   s
% )
% where swap! has been defined as:
% (define (swap! s)
%   (let ((ex-car (car s)))
%      (set-car! s (cdr s))
%      (set-cdr! s ex-car)
%      s
%   )
% )


gma089864(X0,Y0) :-
  cons(X1,X2,X0),
  cons(A,B,X1),
  cons(C,D,X2),
% --
  cons(B,A,Y1),
  cons(D,C,Y2),
  cons(Y1,Y2,Y0),
  !.

% Above clause implies that A=[].
gma089864(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(C,B,Y1),
  cons(A,Y1,Y0),
  !.

% Above clauses implies that C=[].
gma089864(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(B,A,Y1),
  cons(Y1,C,Y0),
  !.

gma089864(X,X). %% Fix the rest, i.e. S-exprs () and (() . ())


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% An alternative version, which shows that the order of the last two clauses
% is insignificant:
% CLAUSE gmA089864b[] = { CLAUSESEQ_begin(103,3), { 3, 2, 2, 7,}, { 2, 1, 1, 1 }, { 2, 0, 0, 2 }  };
% 
% Try: applyGatUptoN(gma089864,196,X), applyGatUptoN(gma089864b,196,Y), X == Y.


gma089864b(X0,Y0) :-
  cons(X1,X2,X0),
  cons(A,B,X1),
  cons(C,D,X2),
% --
  cons(B,A,Y1),
  cons(D,C,Y2),
  cons(Y1,Y2,Y0),
  !.

% Above clauses implies that C=[].
gma089864b(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(B,A,Y1),
  cons(Y1,C,Y0),
  !.

% Above clause implies that A=[].
gma089864b(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(C,B,Y1),
  cons(A,Y1,Y0),
  !.

gma089864b(X,X). %% Fix the rest, i.e. S-exprs () and (() . ())

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% INVKROF(*A069770)
% CLAUSE gmA129604[] = { CLAUSESEQ_begin(103,3), { 3, 2, 2, 20,}, { 2, 0, 1, 4 }, { 2, 1, 0, 4 } }; /* A089840[1654720] */
% ((a . b) . (c . d)) --> ((d . c) . (b . a))
% (a . (b . c))       --> ((c . b) . a)   [a implied ()]
% ((a . b) . c)       --> (c . (b . a))   [c implied ()]
%
% This involution effects the following transformation:
%
%  A  B C  D     D  C B  A       B   C   C   B           A   B            B   A
%   \ / \ /       \ / \ /         \ /     \ /             \ /              \ /
%    X1  X2   -->  Y1  Y2      A   X1  --> Y1  A           X1  C  -->   C   Y1
%     \ /           \ /         \ /         \ /             \ /          \ /
%      X0            Y0          X0          Y0              X0           Y0
%

% A129604 = A069770 o A089864 = A089864 o A069770

% In Scheme this can be defined just as:
% (define (*A129604! s)
%   (cond ((pair? s)
%            (*A069770! (car s))
%            (*A069770! (cdr s))
%            (*A069770! s)
%         )
%   )
%   s
% )


gma129604(X0,Y0) :-
  cons(X1,X2,X0),
  cons(A,B,X1),
  cons(C,D,X2),
% --
  cons(D,C,Y1),
  cons(B,A,Y2),
  cons(Y1,Y2,Y0),
  !.

% Above clause implies that A=[].
gma129604(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(C,B,Y1),
  cons(Y1,A,Y0),
  !.

% Above clauses implies that C=[].
gma129604(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(B,A,Y1),
  cons(C,Y1,Y0),
  !.

gma129604(X,X). %% Fix the rest, i.e. S-exprs () and (() . ())


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% CLAUSE gmA123497[] = { CLAUSESEQ_begin(103,3), { 3, 3, 1, 6,}, { 2, 1, 1, 2 }, { 2, 0, 0, 1 } }; /* A089840[1655089] */
% ((a . (b . c)) . d) --> (a . ((b . d) . c))
% ((a . b) . c) --> ((a . c) . b)
% (a . (b . c)) --> (b . (a . c))
%
%   B   C         B   D
%    \ /           \ /
% A   X2            Y2  C  A  []        A   C           B   C           []  C
%  \ /               \ /    \ /          \ /             \ /             \ /
%   X1  D  -->    A   Y1    X1   C   -->  Y1 []      []   X1   -->    B  Y1
%    \ /           \ /        \ /          \ /         \ /             \ /
%     X0            Y0         X0           Y0          X0              Y0


gma123497(X0,Y0) :-
  cons(X1,D,X0),
  cons(A,X2,X1),
  cons(B,C,X2),
% --
  cons(B,D,Y2),
  cons(Y2,C,Y1),
  cons(A,Y1,Y0),
  !.

gma123497(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(A,C,Y1),
  cons(Y1,B,Y0),
  !.

gma123497(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,C,Y1),
  cons(B,Y1,Y0),
  !.

gma123497(X,X).

% Scheme definition:
% (define (*A123497! s)
%   (cond ((null? s) s)
%         ((and (pair? (car s)) (pair? (cdar s)))
%             (*A074680! s)
%             (let ((old-cddr-s (cddr s)))
%                (set-cdr! (cdr s) (cdadr s))
%                (set-cdr! (cadr s) old-cddr-s)
%             )
%         )
%         ((pair? (car s)) (*A072797! s))
%         ((pair? (cdr s)) (*A072796! s))
%   )
%   s
% )
% 
% 

%% CLAUSE gmA123498[] = { CLAUSESEQ_begin(103,3), { 3, 1, 3, 6,}, { 2, 0, 0, 1 }, { 2, 1, 1, 2 } }; /* A089840[1654249] */
% (a . ((b . c) . d)) --> ((a . (b . d)) . c)
% (a . (b . c)) --> (b . (a . c))
% ((a . b) . c) --> ((a . c) . b)
%
%   B   C         B   D
%    \ /           \ /
%     X2  D     A   Y2         []  C        A   C   A   B           A   []
%      \ /       \ /            \ /          \ /     \ /             \ /
%   A  X1  -->    Y1  C      A   X1  -->  []  Y1      X1  []   -->    Y1  B
%    \ /           \ /        \ /          \ /         \ /             \ /
%     X0            Y0         X0           Y0          X0              Y0


gma123498(X0,Y0) :-
  cons(A,X1,X0),
  cons(X2,D,X1),
  cons(B,C,X2),
% --
  cons(B,D,Y2),
  cons(A,Y2,Y1),
  cons(Y1,C,Y0),
  !.

gma123498(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,C,Y1),
  cons(B,Y1,Y0),
  !.

gma123498(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(A,C,Y1),
  cons(Y1,B,Y0),
  !.

gma123498(X,X).


% Scheme definition:
% (define (*A123498! s)
%   (cond ((null? s) s)
%         ((and (pair? (cdr s)) (pair? (cadr s)))
%             (let ((old-cddr-s (cddr s)))
%                (set-cdr! (cdr s) (cdadr s))
%                (set-cdr! (cadr s) old-cddr-s)
%             )
%             (*A074679! s)
%         )
%         ((pair? (cdr s)) (*A072796! s))
%         ((pair? (car s)) (*A072797! s))
%   )
%   s
% )


% CLAUSE gmA123695[] =  { CLAUSESEQ_begin(99,3), { 2, 0, 1, 0,}, { 3, 3, 1, 23,}, { 2, 1, 0, 3 } }; /* A089840[1653002] */
% Non-canonical form:
% CLAUSE gmA123695b[] = { CLAUSESEQ_begin(99,3), { 2, 0, 1, 0,}, { 3, 3, 1, 23,}, { 2, 1, 0, 4 } };
% (a . (b . c)) --> ((a . b) . c)
% ((a . (b . c)) . d) --> (d . ((a . b) . c))
% ((a . b) . c) --> (b . (c . a))
% In variant b, the last clause is replaced with:
% ((a . b) . c) --> (c . (b . a))
%
%                            B   C        A   B
%                             \ /          \ /
%   B   C     A   B        A   X2           Y2  C   A  []               []  A
%    \ /       \ /          \ /              \ /     \ /                 \ /
% A   X1   -->  Y1  C        X1 []   -->  []  Y1      X1 []    -->    []  Y1
%  \ /           \ /          \ /          \ /         \ /             \ /
%   X0            Y0           X0           Y0          X0              Y0
%


% Scheme definition:
% (define (*A123695! s)
%   (cond ((null? s) s)
%         ((pair? (cdr s)) (*A074679! s))
%         ((pair? (car s)) (*A074679! (car s)) (*A069770! s))
%   )
%   s
% )


gma123695(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(A,B,Y1),
  cons(Y1,C,Y0),
  !.

% D implied [].
gma123695(X0,Y0) :-
  cons(X1,D,X0),
  cons(A,X2,X1),
  cons(B,C,X2),
% --
  cons(A,B,Y2),
  cons(Y2,C,Y1),
  cons(D,Y1,Y0),
  !.

% B and C implied [].
gma123695(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(C,A,Y1),
  cons(B,Y1,Y0),
  !.

%% In the alternative version, the last non-default clause would be:
%%
%% gma123695(X0,Y0) :-
%%   cons(X1,C,X0),
%%   cons(A,B,X1),
%% % --
%%   cons(B,A,Y1),
%%   cons(C,Y1,Y0),
%%   !.

gma123695(X,X).



%% CLAUSE gmA123696[] = { CLAUSESEQ_begin(99,3), { 2, 1, 0, 0,}, { 3, 1, 3, 9,}, { 2, 0, 1, 4 } }; /* A089840[1653063] */
% ((a . b) . c)       --> (a . (b . c))
% (a . ((b . c) . d)) --> ((b . (c . d)) . a)
% (a . (b . c))       --> ((c . b) . a)
%
%                            B   C       C   D
%                             \ /         \ /
% A   B             B   C      X2  D    B  Y2           []   C      C   []
%  \ /               \ /        \ /      \ /             \ /         \ /
%   X1  C  -->    A   Y1     []  X1  -->  Y1 []      []   X1   -->    Y1  []
%    \ /           \ /        \ /          \ /         \ /             \ /
%     X0            Y0         X0           Y0          X0              Y0

% Scheme definition:
% (define (*A123696! s)
%   (cond ((null? s) s)
%         ((pair? (car s)) (*A074680! s))
%         ((pair? (cdr s)) (*A074680! (cdr s)) (*A069770! s))
%   )
%   s
% )

gma123696(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(B,C,Y1),
  cons(A,Y1,Y0),
  !.

gma123696(X0,Y0) :-
  cons(A,X1,X0),
  cons(X2,D,X1),
  cons(B,C,X2),
% --
  cons(C,D,Y2),
  cons(B,Y2,Y1),
  cons(Y1,A,Y0),
  !.

gma123696(X0,Y0) :-
  cons(A,X1,X0),
  cons(B,C,X1),
% --
  cons(C,B,Y1),
  cons(Y1,A,Y0),
  !.

gma123696(X,X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                                                    %%
%% Two examples out of 1017174 non-recursive automorphisms with       %%
%% two non-default clauses of total 7 opening (closing) conses.       %%
%%                                                                    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% CLAUSE gmA123713[] = { CLAUSESEQ_begin(124,2), { 2, 1, 1, 3,}, { 5, 13, 13, 152 } }; /* A089840[1783367] */

% ((a . b) . c)                   --> ((b . c) . a)  (c.f. A089855)
% (a . ((((b . c) . d) . e) . f)) --> (a . ((((c . d) . e) . f) . b))
%
%
%  A   B         B   C
%   \ /           \ /
%    X1  C   -->   Y1  A
%     \ /           \ /
%      X0            Y0
%
%  B   C            C   D
%   \ /              \ /
%    X4  D            Y4  E
%     \ /              \ /
%      X3  E            Y3  F
%       \ /     -->      \ /
%        X2  F            Y2  B
%         \ /              \ /
%      []  X1           []  Y1
%       \ /              \ /
%        X0               Y0
%


gma123713(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(B,C,Y1),
  cons(Y1,A,Y0),
  !.

gma123713(X0,Y0) :-
  cons(A,X1,X0),
  cons(X2,F,X1),
  cons(X3,E,X2),
  cons(X4,D,X3),
  cons(B,C,X4),
% --
  cons(C,D,Y4),
  cons(Y4,E,Y3),
  cons(Y3,F,Y2),
  cons(Y2,B,Y1),
  cons(A,Y1,Y0),
  !.

gma123713(X,X).



% CLAUSE gmA123714[] = { CLAUSESEQ_begin(124,2), { 2, 1, 1, 5,}, { 5, 13, 13, 566 } }; /* A089840[1786785] */

% ((a . b) . c) --> ((c . a) . b)  (c.f. A089857)
% (a . ((((b . c) . d) . e) . f)) --> (a . ((((f . b) . c) . d) . e))
% 
%
%  A   B         C   A
%   \ /           \ /
%    X1  C   -->   Y1  B
%     \ /           \ /
%      X0            Y0
%
%
%  B   C            F   B
%   \ /              \ /
%    X4  D            Y4  C
%     \ /              \ /
%      X3  E            Y3  D
%       \ /     -->      \ /
%        X2  F            Y2  E
%         \ /              \ /
%      []  X1           []  Y1
%       \ /              \ /
%        X0               Y0
%


gma123714(X0,Y0) :-
  cons(X1,C,X0),
  cons(A,B,X1),
% --
  cons(C,A,Y1),
  cons(Y1,B,Y0),
  !.

gma123714(X0,Y0) :-
  cons(A,X1,X0),
  cons(X2,F,X1),
  cons(X3,E,X2),
  cons(X4,D,X3),
  cons(B,C,X4),
% --
  cons(F,B,Y4),
  cons(Y4,C,Y3),
  cons(Y3,D,Y2),
  cons(Y2,E,Y1),
  cons(A,Y1,Y0),
  !.

gma123714(X,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

applygat(gma001477,X,Y) :-
  gma001477(X,Y).

applygat(gma069770,X,Y) :-
  gma069770(X,Y).

applygat(gma072796,X,Y) :-
  gma072796(X,Y).

applygat(gma089850,X,Y) :-
  gma089850(X,Y).

applygat(gma089851,X,Y) :-
  gma089851(X,Y).

applygat(gma089852,X,Y) :-
  gma089852(X,Y).

applygat(gma089853,X,Y) :-
  gma089853(X,Y).

applygat(gma089854,X,Y) :-
  gma089854(X,Y).

applygat(gma072797,X,Y) :-
  gma072797(X,Y).

applygat(gma089855,X,Y) :-
  gma089855(X,Y).

applygat(gma089856,X,Y) :-
  gma089856(X,Y).

applygat(gma089857,X,Y) :-
  gma089857(X,Y).

applygat(gma074679,X,Y) :-
  gma074679(X,Y).

applygat(gma089858,X,Y) :-
  gma089858(X,Y).

applygat(gma073269,X,Y) :-
  gma073269(X,Y).

applygat(gma089859,X,Y) :-
  gma089859(X,Y).

applygat(gma089860,X,Y) :-
  gma089860(X,Y).

applygat(gma074680,X,Y) :-
  gma074680(X,Y).

applygat(gma089861,X,Y) :-
  gma089861(X,Y).

applygat(gma073270,X,Y) :-
  gma073270(X,Y).

applygat(gma089862,X,Y) :-
  gma089862(X,Y).

applygat(gma089863,X,Y) :-
  gma089863(X,Y).

applygat(gma082354,X,Y) :-
  gma082354(X,Y).

applygat(gma082353,X,Y) :-
  gma082353(X,Y).

applygat(gma082351,X,Y) :-
  gma082351(X,Y).

applygat(gma082352,X,Y) :-
  gma082352(X,Y).

applygat(gma073281,X,Y) :-
  gma073281(X,Y).

applygat(gma089864,X,Y) :-
  gma089864(X,Y).

applygat(gma089864b,X,Y) :-
  gma089864b(X,Y).

applygat(gma123492,X,Y) :-
  gma123492(X,Y).

applygat(gma123492b,X,Y) :-
  gma123492b(X,Y).

applygat(gma123495,X,Y) :-
  gma123495(X,Y).

applygat(gma123496,X,Y) :-
  gma123496(X,Y).

applygat(gma123497,X,Y) :-
  gma123497(X,Y).

applygat(gma123498,X,Y) :-
  gma123498(X,Y).

applygat(gma123499,X,Y) :-
  gma123499(X,Y).

applygat(gma123500,X,Y) :-
  gma123500(X,Y).

applygat(gma123503,X,Y) :-
  gma123503(X,Y).

applygat(gma123695,X,Y) :-
  gma123695(X,Y).

applygat(gma123696,X,Y) :-
  gma123696(X,Y).

applygat(gma123713,X,Y) :-
  gma123713(X,Y).

applygat(gma123714,X,Y) :-
  gma123714(X,Y).

applygat(gma129604,X,Y) :-
  gma129604(X,Y).

applygat(gma129605,X,Y) :-
  gma129605(X,Y).

applygat(gma129606,X,Y) :-
  gma129606(X,Y).

applygat(gma129607,X,Y) :-
  gma129607(X,Y).

applygat(gma129609,X,Y) :-
  gma129609(X,Y).

applygat(gma129610,X,Y) :-
  gma129610(X,Y).

applygat(gma129611,X,Y) :-
  gma129611(X,Y).

applygat(gma129612,X,Y) :-
  gma129612(X,Y).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

signatperm(gma001477,U,X) :-
   applyGatUptoN(gma001477,U,X).

signatperm(gma069770,U,X) :-
   applyGatUptoN(gma069770,U,X).

signatperm(gma072796,U,X) :-
  applyGatUptoN(gma072796,U,X).

signatperm(gma089850,U,X) :-
  applyGatUptoN(gma089850,U,X).

signatperm(gma089851,U,X) :-
  applyGatUptoN(gma089851,U,X).

signatperm(gma089852,U,X) :-
  applyGatUptoN(gma089852,U,X).

signatperm(gma089853,U,X) :-
  applyGatUptoN(gma089853,U,X).

signatperm(gma089854,U,X) :-
  applyGatUptoN(gma089854,U,X).

signatperm(gma072797,U,X) :-
  applyGatUptoN(gma072797,U,X).

signatperm(gma089855,U,X) :-
  applyGatUptoN(gma089855,U,X).

signatperm(gma089856,U,X) :-
  applyGatUptoN(gma089856,U,X).

signatperm(gma089857,U,X) :-
  applyGatUptoN(gma089857,U,X).

signatperm(gma074679,U,X) :-
  applyGatUptoN(gma074679,U,X).

signatperm(gma089858,U,X) :-
  applyGatUptoN(gma089858,U,X).

signatperm(gma073269,U,X) :-
  applyGatUptoN(gma073269,U,X).

signatperm(gma089859,U,X) :-
  applyGatUptoN(gma089859,U,X).

signatperm(gma089860,U,X) :-
  applyGatUptoN(gma089860,U,X).

signatperm(gma074680,U,X) :-
  applyGatUptoN(gma074680,U,X).

signatperm(gma089861,U,X) :-
  applyGatUptoN(gma089861,U,X).

signatperm(gma073270,U,X) :-
  applyGatUptoN(gma073270,U,X).

signatperm(gma089862,U,X) :-
  applyGatUptoN(gma089862,U,X).

signatperm(gma089863,U,X) :-
  applyGatUptoN(gma089863,U,X).

signatperm(gma082354,U,X) :-
  applyGatUptoN(gma082354,U,X).

signatperm(gma082353,U,X) :-
  applyGatUptoN(gma082353,U,X).

signatperm(gma082351,U,X) :-
  applyGatUptoN(gma082351,U,X).

signatperm(gma082352,U,X) :-
  applyGatUptoN(gma082352,U,X).

signatperm(gma073281,U,X) :-
  applyGatUptoN(gma073281,U,X).

signatperm(gma089864,U,X) :-
  applyGatUptoN(gma089864,U,X).

signatperm(gma089864b,U,X) :-
  applyGatUptoN(gma089864b,U,X).

signatperm(gma123492,U,X) :-
  applyGatUptoN(gma123492,U,X).

signatperm(gma123492b,U,X) :-
  applyGatUptoN(gma123492b,U,X).

signatperm(gma123495,U,X) :-
  applyGatUptoN(gma123495,U,X).

signatperm(gma123496,U,X) :-
  applyGatUptoN(gma123496,U,X).

signatperm(gma123497,U,X) :-
  applyGatUptoN(gma123497,U,X).

signatperm(gma123498,U,X) :-
  applyGatUptoN(gma123498,U,X).

signatperm(gma123499,U,X) :-
  applyGatUptoN(gma123499,U,X).

signatperm(gma123500,U,X) :-
  applyGatUptoN(gma123500,U,X).

signatperm(gma123503,U,X) :-
  applyGatUptoN(gma123503,U,X).

signatperm(gma123695,U,X) :-
  applyGatUptoN(gma123695,U,X).

signatperm(gma123696,U,X) :-
  applyGatUptoN(gma123696,U,X).

signatperm(gma123713,U,X) :-
  applyGatUptoN(gma123713,U,X).

signatperm(gma123714,U,X) :-
  applyGatUptoN(gma123714,U,X).

signatperm(gma129604,U,X) :-
  applyGatUptoN(gma129604,U,X).

signatperm(gma129605,U,X) :-
  applyGatUptoN(gma129605,U,X).

signatperm(gma129606,U,X) :-
  applyGatUptoN(gma129606,U,X).

signatperm(gma129607,U,X) :-
  applyGatUptoN(gma129607,U,X).

signatperm(gma129609,U,X) :-
  applyGatUptoN(gma129609,U,X).

signatperm(gma129610,U,X) :-
  applyGatUptoN(gma129610,U,X).

signatperm(gma129611,U,X) :-
  applyGatUptoN(gma129611,U,X).

signatperm(gma129612,U,X) :-
  applyGatUptoN(gma129612,U,X).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

applyGatToN(X,G,Y) :-
   n2s(X,S),
   applygat(G,S,T),
   n2s(Y,T).

applyGatUptoN(G,U,W) :-
   applyGatUptoNaux(G,U,[],W).

applyGatUptoNaux(_,-1,W,W) :-
   !.

applyGatUptoNaux(G,U,Zs,W) :-
   applyGatToN(U,G,Z),
   V is U-1,
   applyGatUptoNaux(G,V,[Z|Zs],W).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%
%% This table prepared with Scheme function (prepare-prolog-table 196)
%% For the source see:
%% http://www.iki.fi/~kartturi/matikka/Nekomorphisms/gatorank.scm

%% We use green cuts as this is injective mapping:

n2s(0,[]) :-
  !.
n2s(1,[[]]) :-
  !.
n2s(2,[[],[]]) :-
  !.
n2s(3,[[[]]]) :-
  !.
n2s(4,[[],[],[]]) :-
  !.
n2s(5,[[],[[]]]) :-
  !.
n2s(6,[[[]],[]]) :-
  !.
n2s(7,[[[],[]]]) :-
  !.
n2s(8,[[[[]]]]) :-
  !.
n2s(9,[[],[],[],[]]) :-
  !.
n2s(10,[[],[],[[]]]) :-
  !.
n2s(11,[[],[[]],[]]) :-
  !.
n2s(12,[[],[[],[]]]) :-
  !.
n2s(13,[[],[[[]]]]) :-
  !.
n2s(14,[[[]],[],[]]) :-
  !.
n2s(15,[[[]],[[]]]) :-
  !.
n2s(16,[[[],[]],[]]) :-
  !.
n2s(17,[[[],[],[]]]) :-
  !.
n2s(18,[[[],[[]]]]) :-
  !.
n2s(19,[[[[]]],[]]) :-
  !.
n2s(20,[[[[]],[]]]) :-
  !.
n2s(21,[[[[],[]]]]) :-
  !.
n2s(22,[[[[[]]]]]) :-
  !.
n2s(23,[[],[],[],[],[]]) :-
  !.
n2s(24,[[],[],[],[[]]]) :-
  !.
n2s(25,[[],[],[[]],[]]) :-
  !.
n2s(26,[[],[],[[],[]]]) :-
  !.
n2s(27,[[],[],[[[]]]]) :-
  !.
n2s(28,[[],[[]],[],[]]) :-
  !.
n2s(29,[[],[[]],[[]]]) :-
  !.
n2s(30,[[],[[],[]],[]]) :-
  !.
n2s(31,[[],[[],[],[]]]) :-
  !.
n2s(32,[[],[[],[[]]]]) :-
  !.
n2s(33,[[],[[[]]],[]]) :-
  !.
n2s(34,[[],[[[]],[]]]) :-
  !.
n2s(35,[[],[[[],[]]]]) :-
  !.
n2s(36,[[],[[[[]]]]]) :-
  !.
n2s(37,[[[]],[],[],[]]) :-
  !.
n2s(38,[[[]],[],[[]]]) :-
  !.
n2s(39,[[[]],[[]],[]]) :-
  !.
n2s(40,[[[]],[[],[]]]) :-
  !.
n2s(41,[[[]],[[[]]]]) :-
  !.
n2s(42,[[[],[]],[],[]]) :-
  !.
n2s(43,[[[],[]],[[]]]) :-
  !.
n2s(44,[[[],[],[]],[]]) :-
  !.
n2s(45,[[[],[],[],[]]]) :-
  !.
n2s(46,[[[],[],[[]]]]) :-
  !.
n2s(47,[[[],[[]]],[]]) :-
  !.
n2s(48,[[[],[[]],[]]]) :-
  !.
n2s(49,[[[],[[],[]]]]) :-
  !.
n2s(50,[[[],[[[]]]]]) :-
  !.
n2s(51,[[[[]]],[],[]]) :-
  !.
n2s(52,[[[[]]],[[]]]) :-
  !.
n2s(53,[[[[]],[]],[]]) :-
  !.
n2s(54,[[[[]],[],[]]]) :-
  !.
n2s(55,[[[[]],[[]]]]) :-
  !.
n2s(56,[[[[],[]]],[]]) :-
  !.
n2s(57,[[[[],[]],[]]]) :-
  !.
n2s(58,[[[[],[],[]]]]) :-
  !.
n2s(59,[[[[],[[]]]]]) :-
  !.
n2s(60,[[[[[]]]],[]]) :-
  !.
n2s(61,[[[[[]]],[]]]) :-
  !.
n2s(62,[[[[[]],[]]]]) :-
  !.
n2s(63,[[[[[],[]]]]]) :-
  !.
n2s(64,[[[[[[]]]]]]) :-
  !.
n2s(65,[[],[],[],[],[],[]]) :-
  !.
n2s(66,[[],[],[],[],[[]]]) :-
  !.
n2s(67,[[],[],[],[[]],[]]) :-
  !.
n2s(68,[[],[],[],[[],[]]]) :-
  !.
n2s(69,[[],[],[],[[[]]]]) :-
  !.
n2s(70,[[],[],[[]],[],[]]) :-
  !.
n2s(71,[[],[],[[]],[[]]]) :-
  !.
n2s(72,[[],[],[[],[]],[]]) :-
  !.
n2s(73,[[],[],[[],[],[]]]) :-
  !.
n2s(74,[[],[],[[],[[]]]]) :-
  !.
n2s(75,[[],[],[[[]]],[]]) :-
  !.
n2s(76,[[],[],[[[]],[]]]) :-
  !.
n2s(77,[[],[],[[[],[]]]]) :-
  !.
n2s(78,[[],[],[[[[]]]]]) :-
  !.
n2s(79,[[],[[]],[],[],[]]) :-
  !.
n2s(80,[[],[[]],[],[[]]]) :-
  !.
n2s(81,[[],[[]],[[]],[]]) :-
  !.
n2s(82,[[],[[]],[[],[]]]) :-
  !.
n2s(83,[[],[[]],[[[]]]]) :-
  !.
n2s(84,[[],[[],[]],[],[]]) :-
  !.
n2s(85,[[],[[],[]],[[]]]) :-
  !.
n2s(86,[[],[[],[],[]],[]]) :-
  !.
n2s(87,[[],[[],[],[],[]]]) :-
  !.
n2s(88,[[],[[],[],[[]]]]) :-
  !.
n2s(89,[[],[[],[[]]],[]]) :-
  !.
n2s(90,[[],[[],[[]],[]]]) :-
  !.
n2s(91,[[],[[],[[],[]]]]) :-
  !.
n2s(92,[[],[[],[[[]]]]]) :-
  !.
n2s(93,[[],[[[]]],[],[]]) :-
  !.
n2s(94,[[],[[[]]],[[]]]) :-
  !.
n2s(95,[[],[[[]],[]],[]]) :-
  !.
n2s(96,[[],[[[]],[],[]]]) :-
  !.
n2s(97,[[],[[[]],[[]]]]) :-
  !.
n2s(98,[[],[[[],[]]],[]]) :-
  !.
n2s(99,[[],[[[],[]],[]]]) :-
  !.
n2s(100,[[],[[[],[],[]]]]) :-
  !.
n2s(101,[[],[[[],[[]]]]]) :-
  !.
n2s(102,[[],[[[[]]]],[]]) :-
  !.
n2s(103,[[],[[[[]]],[]]]) :-
  !.
n2s(104,[[],[[[[]],[]]]]) :-
  !.
n2s(105,[[],[[[[],[]]]]]) :-
  !.
n2s(106,[[],[[[[[]]]]]]) :-
  !.
n2s(107,[[[]],[],[],[],[]]) :-
  !.
n2s(108,[[[]],[],[],[[]]]) :-
  !.
n2s(109,[[[]],[],[[]],[]]) :-
  !.
n2s(110,[[[]],[],[[],[]]]) :-
  !.
n2s(111,[[[]],[],[[[]]]]) :-
  !.
n2s(112,[[[]],[[]],[],[]]) :-
  !.
n2s(113,[[[]],[[]],[[]]]) :-
  !.
n2s(114,[[[]],[[],[]],[]]) :-
  !.
n2s(115,[[[]],[[],[],[]]]) :-
  !.
n2s(116,[[[]],[[],[[]]]]) :-
  !.
n2s(117,[[[]],[[[]]],[]]) :-
  !.
n2s(118,[[[]],[[[]],[]]]) :-
  !.
n2s(119,[[[]],[[[],[]]]]) :-
  !.
n2s(120,[[[]],[[[[]]]]]) :-
  !.
n2s(121,[[[],[]],[],[],[]]) :-
  !.
n2s(122,[[[],[]],[],[[]]]) :-
  !.
n2s(123,[[[],[]],[[]],[]]) :-
  !.
n2s(124,[[[],[]],[[],[]]]) :-
  !.
n2s(125,[[[],[]],[[[]]]]) :-
  !.
n2s(126,[[[],[],[]],[],[]]) :-
  !.
n2s(127,[[[],[],[]],[[]]]) :-
  !.
n2s(128,[[[],[],[],[]],[]]) :-
  !.
n2s(129,[[[],[],[],[],[]]]) :-
  !.
n2s(130,[[[],[],[],[[]]]]) :-
  !.
n2s(131,[[[],[],[[]]],[]]) :-
  !.
n2s(132,[[[],[],[[]],[]]]) :-
  !.
n2s(133,[[[],[],[[],[]]]]) :-
  !.
n2s(134,[[[],[],[[[]]]]]) :-
  !.
n2s(135,[[[],[[]]],[],[]]) :-
  !.
n2s(136,[[[],[[]]],[[]]]) :-
  !.
n2s(137,[[[],[[]],[]],[]]) :-
  !.
n2s(138,[[[],[[]],[],[]]]) :-
  !.
n2s(139,[[[],[[]],[[]]]]) :-
  !.
n2s(140,[[[],[[],[]]],[]]) :-
  !.
n2s(141,[[[],[[],[]],[]]]) :-
  !.
n2s(142,[[[],[[],[],[]]]]) :-
  !.
n2s(143,[[[],[[],[[]]]]]) :-
  !.
n2s(144,[[[],[[[]]]],[]]) :-
  !.
n2s(145,[[[],[[[]]],[]]]) :-
  !.
n2s(146,[[[],[[[]],[]]]]) :-
  !.
n2s(147,[[[],[[[],[]]]]]) :-
  !.
n2s(148,[[[],[[[[]]]]]]) :-
  !.
n2s(149,[[[[]]],[],[],[]]) :-
  !.
n2s(150,[[[[]]],[],[[]]]) :-
  !.
n2s(151,[[[[]]],[[]],[]]) :-
  !.
n2s(152,[[[[]]],[[],[]]]) :-
  !.
n2s(153,[[[[]]],[[[]]]]) :-
  !.
n2s(154,[[[[]],[]],[],[]]) :-
  !.
n2s(155,[[[[]],[]],[[]]]) :-
  !.
n2s(156,[[[[]],[],[]],[]]) :-
  !.
n2s(157,[[[[]],[],[],[]]]) :-
  !.
n2s(158,[[[[]],[],[[]]]]) :-
  !.
n2s(159,[[[[]],[[]]],[]]) :-
  !.
n2s(160,[[[[]],[[]],[]]]) :-
  !.
n2s(161,[[[[]],[[],[]]]]) :-
  !.
n2s(162,[[[[]],[[[]]]]]) :-
  !.
n2s(163,[[[[],[]]],[],[]]) :-
  !.
n2s(164,[[[[],[]]],[[]]]) :-
  !.
n2s(165,[[[[],[]],[]],[]]) :-
  !.
n2s(166,[[[[],[]],[],[]]]) :-
  !.
n2s(167,[[[[],[]],[[]]]]) :-
  !.
n2s(168,[[[[],[],[]]],[]]) :-
  !.
n2s(169,[[[[],[],[]],[]]]) :-
  !.
n2s(170,[[[[],[],[],[]]]]) :-
  !.
n2s(171,[[[[],[],[[]]]]]) :-
  !.
n2s(172,[[[[],[[]]]],[]]) :-
  !.
n2s(173,[[[[],[[]]],[]]]) :-
  !.
n2s(174,[[[[],[[]],[]]]]) :-
  !.
n2s(175,[[[[],[[],[]]]]]) :-
  !.
n2s(176,[[[[],[[[]]]]]]) :-
  !.
n2s(177,[[[[[]]]],[],[]]) :-
  !.
n2s(178,[[[[[]]]],[[]]]) :-
  !.
n2s(179,[[[[[]]],[]],[]]) :-
  !.
n2s(180,[[[[[]]],[],[]]]) :-
  !.
n2s(181,[[[[[]]],[[]]]]) :-
  !.
n2s(182,[[[[[]],[]]],[]]) :-
  !.
n2s(183,[[[[[]],[]],[]]]) :-
  !.
n2s(184,[[[[[]],[],[]]]]) :-
  !.
n2s(185,[[[[[]],[[]]]]]) :-
  !.
n2s(186,[[[[[],[]]]],[]]) :-
  !.
n2s(187,[[[[[],[]]],[]]]) :-
  !.
n2s(188,[[[[[],[]],[]]]]) :-
  !.
n2s(189,[[[[[],[],[]]]]]) :-
  !.
n2s(190,[[[[[],[[]]]]]]) :-
  !.
n2s(191,[[[[[[]]]]],[]]) :-
  !.
n2s(192,[[[[[[]]]],[]]]) :-
  !.
n2s(193,[[[[[[]]],[]]]]) :-
  !.
n2s(194,[[[[[[]],[]]]]]) :-
  !.
n2s(195,[[[[[[],[]]]]]]) :-
  !.
n2s(196,[[[[[[[]]]]]]]) :-
  !.

