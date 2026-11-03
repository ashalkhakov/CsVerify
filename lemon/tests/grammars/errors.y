// Errors the reader must report: an unknown directive, a bad alias, a missing rule end, an undefined start.
%token_type {int}
%bogus_directive foo
start ::= a(X) b(X).
a ::= A
b ::= B.
c ::= C(.
