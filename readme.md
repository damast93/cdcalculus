# CD-Calculus

The [CD calculus](https://dario-stein.de/notes/thesis.pdf) is a simple first-order programming language, which can construct and match pairs and call functions
```
s,t ::= x | () | (s,t) | f t | let x = s in t | match (x,y) = s in t 
```

Such terms can be interpreted semantically in every CD category. We provide a simple compiler from CD calculus terms to morphisms, as represented in the proof assistant [Chyp](https://github.com/akissinger/chyp). We can then use Chyp to visualize and simplify these morphisms as string diagrams.

![Chyp Example](https://raw.githubusercontent.com/damast93/cdcalculus/main/img/semantics.png)