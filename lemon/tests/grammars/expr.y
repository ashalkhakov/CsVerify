/* An unambiguous expression grammar: no precedence declarations, no conflicts (the completeness validator passes). */
%token_type {int}
%start_symbol program
program ::= expr.
expr ::= expr PLUS term.
expr ::= term.
term ::= term TIMES factor.
term ::= factor.
factor ::= LPAREN expr RPAREN.
factor ::= NUM.
