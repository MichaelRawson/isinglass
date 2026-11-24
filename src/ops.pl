% operators of the internal syntax, imported by modules that pattern-match on formulas or proofs
% quantifiers are written '!'(B, F) and '?'(B, F), with a binder B of the form X : Sort (a prefix '!'
% operator would break cuts in Scryer); ':' has the priority of SWI's, not TPTP's, so that
% module-qualified goals parse as usual; M @ N is the application of a proof term (ir.pl)
:- module(ops, [
  op(200, xfy, :),
  op(200, yfx, @),
  op(450, fy, ~),
  op(1102, xfy, '|'),
  op(1103, xfy, &),
  op(1104, xfx, =>),
  op(1105, xfx, <=>)
]).
