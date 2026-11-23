# Layered

A solution laid out as applications usually are: a domain project (`Layered.Model`), a data project with the Entity
Framework context (`Layered.Data`), and the application's code (`Layered.App`), which references both. Model and
Data set `CsVerifyExclude`; App is verified, and the others are compiled as projects of their own that its
compilation references (the build targets describe them). `samples/e2e.sh` verifies it with the packages as users get them, and every method of App must
verify.

Each file of App holds the code of an issue that the layout brought up: what goes wrong only when a type, a
context or a contract is declared in another project. A new one of those goes here, with its expected result.
