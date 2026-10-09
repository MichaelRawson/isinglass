% connectives of the internal formula syntax, imported by modules that pattern-match on formulas
% quantifiers are written '!'(Bs, F) and '?'(Bs, F), with binders Bs of the form X : Sort, as in TPTP
% (a prefix '!' operator would break cuts in Scryer); ':' has the priority of SWI's, not TPTP's,
% so that module-qualified goals parse as usual
:- module(ops, [
  op(200, xfy, :),
  op(450, fy, ~),
  op(1102, xfy, '|'),
  op(1103, xfy, &),
  op(1104, xfx, =>),
  op(1105, xfx, <=>)
]).
