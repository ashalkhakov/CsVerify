/* Unambiguous, with empty rules, left and right recursion and a multiterminal (the completeness validator passes). */
%token_type {int}
%start_symbol program
program ::= decls.
decls ::= .
decls ::= decls decl.
decl ::= ID|NAME EQ value SEMI.
value ::= NUM.
value ::= LBRACE items RBRACE.
items ::= .
items ::= value more.
more ::= .
more ::= COMMA value more.
