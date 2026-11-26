/*
Micromath back end: the IR itself, as versioned canonical Prolog data, for Micromath's TPTP replay
(https://git.olsak.net/mirek/Micromath, tptp/IR.md), which reads it in C and proves the original
problem in its own kernel. Isinglass is an untrusted producer there, so nothing is encoded here.

  micromath_ir(1).
  signature(Name, Params, Args, Sort).    one per symbol
  ir_step(Name, Conclusion, Justification).    in dependency order
  end(Refutation).    the last clause([], []), perhaps cited by the conjecture step

The proof is first checked (checker.pl), and a todo step is an error, as Micromath cannot replay a
partial proof.
*/
:- module(micromath, [emit_micromath/0]).
:- use_module(library(lists)).
:- use_module(utils).
:- use_module(db).
:- use_module(ir).
:- use_module(checker).

emit_micromath :-
  findall(ir_step(Name, Conclusion, Justification), ir_step(Name, Conclusion, Justification), Steps),
  maplist(replayable, Steps),
  emit_checker,
  last(Steps, Final),
  final_refutation(Final, Refutation),
  emitted(micromath_ir(1)),
  forall(symbol(Name, Params, Args, Sort), emitted(signature(Name, Params, Args, Sort))),
  maplist(lowered, Steps, Lowered),
  maplist(emitted, Lowered),
  plain_name(Refutation, Plain),
  emitted(end(Plain)).

replayable(ir_step(_, _, Justification)) :- replayable_justification(Justification), !.
replayable(ir_step(Name, _, todo(Record, _))) :- !,
  todo_rule(Record, Rule),
  warn(['error: ', Name, ' (', Rule, ') is not reconstructed, so Micromath cannot replay it']),
  fail.
replayable(ir_step(Name, _, Justification)) :-
  functor(Justification, Kind, _),
  warn(['error: ', Name, ' is justified by ', Kind, ', which Micromath does not replay']),
  fail.

replayable_justification(proof(_)).
replayable_justification(input(_, _)).
replayable_justification(negated_conjecture(_)).
replayable_justification(conjecture(_, _, _)).
replayable_justification(definition(_, _, _)).
replayable_justification(skolem_def(_, _, _)).
replayable_justification(split_def(_, _)).

final_refutation(ir_step(Name, clause([], []), _), Name) :- !.
final_refutation(ir_step(_, formula(_), conjecture(_, _, Refutation)), Refutation) :- !.
final_refutation(ir_step(Name, _, _), _) :-
  warn(['error: the last step ', Name, ' is neither a refutation nor the conjecture']),
  fail.

emitted(Term) :- write_canonical(Term), write('.'), nl.


% Lowering to the stable replay interface: Micromath's reader keeps the forms of the earlier IR, so
% its format does not follow this one. Quantifiers carry binder lists ,
% hypotheses are h(N), applications are app(Head, Terms, Proofs), lemma redexes are let(H, F, M, N),
% and a rewrite is rewrite(X:S, F, Equation, Proof). The parameters of $sym, $refl and $dne are
% left for the reader to infer, as here.
lowered(ir_step(Name, Conclusion, Justification), ir_step(Name1, Conclusion1, Justification1)) :-
  nb_setval(um_hypotheses, 0),
  plain_name(Name, Name1),
  lower_conclusion(Conclusion, Justification, Conclusion1),
  lower_justification(Justification, Justification1).

lower_conclusion(Conclusion, _, Lowered) :- lower_term(Conclusion, Lowered).


% Steps, inputs and definitions are named apart from symbols here, but not in the interface.
plain_name(Name, Plain) :- atom(Name), sub_atom(Name, 0, _, After, '$step:'), !, sub_atom(Name, _, After, 0, Plain).
plain_name(Name, Plain) :- atom(Name), sub_atom(Name, 0, _, After, '$input:'), !, sub_atom(Name, _, After, 0, Plain).
plain_name(Name, Plain) :- atom(Name), sub_atom(Name, 0, _, After, '$def:'), !,
  sub_atom(Name, _, After, 0, Symbol), atom_concat(Symbol, '_def', Plain).
plain_name(Name, Name).

lower_justification(input(Role, Name), input(Role, Plain)) :- !, plain_name(Name, Plain).
lower_justification(negated_conjecture(Name), negated_conjecture(Plain)) :- !, plain_name(Name, Plain).
lower_justification(conjecture(Name, Negated, Refutation), conjecture(Name1, Negated1, Refutation1)) :- !,
  plain_name(Name, Name1), plain_name(Negated, Negated1), plain_name(Refutation, Refutation1).

lower_justification(proof(Proof), proof(Lowered)) :- !, lower_proof(Proof, [], Lowered).
lower_justification(Justification, Lowered) :- lower_term(Justification, Lowered).

% Formulas, and anything containing them: single binders become one-element binder lists.
lower_term(Term, Lowered) :-
  compound(Term), Term =.. [Q, Binder, _], quantifier(Q), Binder = (_ : _), !,
  merged_binders(Q, Term, Binders, Body),
  lower_term(Body, Body1),
  Lowered =.. [Q, Binders, Body1].
lower_term(Term, Lowered) :- compound(Term), !,
  Term =.. [Functor|Args], maplist(lower_term, Args, Args1), Lowered =.. [Functor|Args1].
lower_term(Term, Term).

quantifier(!).
quantifier(?).

merged_binders(Q, Term, [Binder|Binders], Body) :-
  Term =.. [Q, Binder, Inner], Binder = (_ : _), !,
  merged_binders(Q, Inner, Binders, Body).
merged_binders(_, Body, [], Body).

next_hypothesis(N) :- nb_getval(um_hypotheses, N), N1 is N + 1, nb_setval(um_hypotheses, N1).

% Env: list of Index-Kind for the variables '$VAR'(Index), Kind being hyp(N) or object.
lower_proof('$lam'('$VAR'(V), Annotation, Body), Env, Lowered) :- !,
  (   hypothesis_annotation(Annotation, Type)
  ->  next_hypothesis(N), Kind = hyp(N), Binder = h(N), Annotation1 = Type
  ;   Kind = object, Binder = '$VAR'(V), lower_term(Annotation, Annotation1)
  ),
  lower_proof(Body, [V-Kind|Env], Body1),
  Lowered = lam(Binder, Annotation1, Body1).
lower_proof(Proof, Env, Lowered) :- Proof = @(_, _), !,
  proof_spine(Proof, Head, Args),
  lower_application(Head, Args, Env, Lowered).
lower_proof('$VAR'(V), Env, h(N)) :- memberchk(V-hyp(N), Env), !.
lower_proof(Atom, _, app(Plain, [], [])) :- atomic(Atom), !, plain_name(Atom, Plain).
lower_proof(Proof, _, _) :- throw(micromath_unsupported(Proof)).

hypothesis_annotation('$inferred', '$inferred').
hypothesis_annotation('$proof'(Formula), Lowered) :- lower_term(Formula, Lowered).

proof_spine(@(F, A), Head, Args) :- !, proof_spine(F, Head, Args0), append(Args0, [A], Args).
proof_spine(Head, Head, []).

lower_application('$lam'('$VAR'(V), Annotation, Body), [Value|Rest], Env, Lowered) :- !,
  Annotation = '$proof'(Formula), lower_term(Formula, Formula1),
  lower_proof(Value, Env, Value1),
  next_hypothesis(N),
  applied(Rest, Body, Applied),
  lower_proof(Applied, [V-hyp(N)|Env], Body1),
  Lowered = let(h(N), Formula1, Value1, Body1).
lower_application('$rewrite', [Motive, Equation, Proof|Rest], Env, Lowered) :- Rest = [_|_], !,
  % the rewritten fact is a function that is applied at once, as optimised; the reader infers its type
  lower_application('$rewrite', [Motive, Equation, Proof], Env, Rewritten),
  next_hypothesis(N),
  lower_proofs(Rest, Env, Rest1),
  Lowered = let(h(N), '$inferred', Rewritten, app(h(N), [], Rest1)).
lower_application('$rewrite', [Motive, Equation, Proof], Env, rewrite(Binder, Formula1, Equation1, Proof1)) :- !,
  Motive = '$abs'(Binder, Formula), lower_term(Formula, Formula1),
  lower_proof(Equation, Env, Equation1), lower_proof(Proof, Env, Proof1).
lower_application('$nex', [Premise, '$lam'('$VAR'(V), Annotation, Body)], Env, Lowered) :-
  hypothesis_annotation(Annotation, Type), !,
  lower_proof(Premise, Env, Premise1),
  next_hypothesis(N),
  lower_proof(Body, [V-hyp(N)|Env], Body1),
  collapsed_nex(h(N), [], Body1, Body2),
  inlined_nex(h(N), Body2, Collapsed),
  Lowered = app('$nex', [], [Premise1, lam(h(N), Type, Collapsed)]).
lower_application(Head, Args, Env, Lowered) :-
  (   Head = '$VAR'(V) -> memberchk(V-hyp(N), Env), Head1 = h(N)
  ;   Head = h(_) -> Head1 = Head
  ;   atomic(Head), plain_name(Head, Head1)
  ),
  leading_terms(Args, Env, Terms, Args1),
  leading_proofs(Args1, Env, Proofs, Rest),
  lower_proofs(Proofs, Env, Proofs1),
  (   Head1 = h(_), Terms = [_|_], Proofs1 = [_|_]
  ->  % a hypothesis is applied to its terms first, then to its proofs
      next_hypothesis(N0),
      Application = let(h(N0), '$inferred', app(Head1, Terms, []), app(h(N0), [], Proofs1))
  ;   Application = app(Head1, Terms, Proofs1)
  ),
  (   Rest == [] -> Lowered = Application
  ;   % a term after a proof, as the optimised IR inlines a lemma: bind the part so far, its type inferred
      next_hypothesis(N1),
      lower_application(h(N1), Rest, Env, Tail),
      Lowered = let(h(N1), '$inferred', Application, Tail)
  ).

leading_proofs([A|As], Env, [A|Ps], Rest) :- \+ is_term(A, Env), !, leading_proofs(As, Env, Ps, Rest).
leading_proofs(Rest, _, [], Rest).

lower_proofs([], _, []).
lower_proofs([P|Ps], Env, [L|Ls]) :- lower_proof(P, Env, L), lower_proofs(Ps, Env, Ls).

applied([], Term, Term).
applied([A|As], Term, Applied) :- applied(As, @(Term, A), Applied).

leading_terms([A|As], Env, [A|Ts], Ps) :- is_term(A, Env), !, leading_terms(As, Env, Ts, Ps).
leading_terms(Ps, _, [], Ps).

is_term('$VAR'(V), Env) :- !, \+ memberchk(V-hyp(_), Env).
is_term(@(_, _), _) :- !, fail.
is_term('$lam'(_, _, _), _) :- !, fail.
is_term(Atom, _) :- atom(Atom), !, \+ proof_constant(Atom).
is_term(_, _).

proof_constant(Atom) :- sub_atom(Atom, 0, _, _, '$step:'), !.
proof_constant(Atom) :- sub_atom(Atom, 0, _, _, '$def:'), !.
proof_constant(Atom) :- memberchk(Atom, ['$sym', '$refl', '$dne', '$trivial', '$and', '$or', '$imp', '$iff',
  '$nand', '$nor', '$nimp', '$niff', '$ex', '$nall', '$nex']).

% $nex peels one quantifier at a time here, and a block at once in the interface: a chain
% $nex H (\P. let G : ~?Ys.F := P x in $nex G (\Q. B)) becomes one $nex whose result is applied to all of
% x, y, ... in the end. Q stands for P, applied to what has been given already.
collapsed_nex(P, Given, let(G, ~(?(_, _)), app(P, [X], []), app('$nex', [], [G, lam(Q, _, Body)])), Collapsed) :- !,
  append(Given, [X], Given1),
  substituted(Body, Q, P, Body1),
  collapsed_nex(P, Given1, Body1, Collapsed).
collapsed_nex(P, Given, let(G, Type, app(P, Xs, []), Body), let(G, Type, app(P, Terms, []), Body)) :- !,
  append(Given, Xs, Terms).
collapsed_nex(_, _, Term, Term).

substituted(Term, From, To, To) :- Term == From, !.
substituted(Term, From, To, Out) :- compound(Term), !,
  Term =.. [F|Args], substituted_list(Args, From, To, Args1), Out =.. [F|Args1].
substituted(Term, _, _, Term).
substituted_list([], _, _, []).
substituted_list([A|As], From, To, [B|Bs]) :- substituted(A, From, To, B), substituted_list(As, From, To, Bs).

% Optimised, the next $nex of a chain takes its premise inline: $nex (P x) (\Q. B), not through a let.
inlined_nex(P, app('$nex', [], [app(P, Xs, []), lam(Q, _, Body)]), Collapsed) :- !,
  reheaded(Body, Q, P, Xs, Body1),
  inlined_nex(P, Body1, Collapsed).
inlined_nex(_, Term, Term).

reheaded(h(N), h(N), P, Xs, app(P, Xs, [])) :- !.
reheaded(app(h(N), Ys, Ps), h(N), P, Xs, app(P, Zs, Ps1)) :- !,
  append(Xs, Ys, Zs), reheaded_list(Ps, h(N), P, Xs, Ps1).
reheaded(Term, Q, P, Xs, Out) :- compound(Term), !,
  Term =.. [F|Args], reheaded_list(Args, Q, P, Xs, Args1), Out =.. [F|Args1].
reheaded(Term, _, _, _, Term).
reheaded_list([], _, _, _, []).
reheaded_list([A|As], Q, P, Xs, [B|Bs]) :- reheaded(A, Q, P, Xs, B), reheaded_list(As, Q, P, Xs, Bs).
