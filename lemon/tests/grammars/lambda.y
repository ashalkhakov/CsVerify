// Empty rules, nullable chains, left and right recursion, an unused nonterminal, a never-reduced rule.
start ::= a b c.
a ::= .
a ::= a A.
b ::= .
b ::= B b.
c ::= opt opt.
opt ::= .
opt ::= C.
unused ::= D.
