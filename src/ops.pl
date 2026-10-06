% connectives of the internal formula syntax, imported by modules that pattern-match on formulas
% quantifiers are written '!'(Xs, F) and '?'(Xs, F): a prefix '!' operator would break cuts in Scryer
:- module(ops, [
  op(450, fy, ~),
  op(1102, xfy, '|'),
  op(1103, xfy, &),
  op(1104, xfx, =>),
  op(1105, xfx, <=>),
  op(1105, xfx, <~>)
]).
