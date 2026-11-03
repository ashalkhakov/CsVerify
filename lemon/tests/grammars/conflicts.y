// Conflicts: some resolved by precedence, some not (shift/reduce and reduce/reduce).
%token_type {int}
%left PLUS MINUS.
%left TIMES.
%right POW.
%nonassoc EQ.
start ::= stmts.
stmts ::= .
stmts ::= stmts stmt SEMI.
stmt ::= expr.
stmt ::= IF expr THEN stmt.
stmt ::= IF expr THEN stmt ELSE stmt.
expr ::= expr PLUS expr.
expr ::= expr MINUS expr.
expr ::= expr TIMES expr.
expr ::= expr POW expr.
expr ::= expr EQ expr.
expr ::= ID.
expr ::= amb.
amb ::= ID.
