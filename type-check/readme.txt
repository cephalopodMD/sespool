PA4 (7 day extension given by Professor Weimer via email correspondence 
with Ben Gilbert (bjg4uc@virginia.edu) in email chain entitled "PA4 
Extension")

For PA4, we chose Haskell as out implementation language. Additionally, 
or possibly as a result of this, the assignment was very difficult, at 
least at first. Having 4 parts to deal with, we decided to split up the
work. One person did the first three (class map, implementation map, 
parent map) and the other did the annotated AST. Because of this split, 
we had two ways of handling data, two different ways of returning data, 
different code styles, and different ways of handling errors.

To build the first three parts and handle class level errors, a data 
structure called the class_map was created. It was basically thrown 
together using lists and tuples, but it got the job done. It broke down 
all lines of the class into sections - name, line information, 
inheritance, lists of attribute lines grouped by class inherited from, 
and similar lists of method lines - as tuples representing each class. 
The signature looked like this:

(String, (String, String, [[[String]]], [[[String]]]))
that is:
(Name, (Line, Inheritance, [ [[attribute line]] ], [ [[method line]] ]))

and could be turned into a map fairly easily (this came in handly 
later). Some helper utility functions were made to simplify item access 
by class name and break down methods as well. This data structure was 
created by splitting up by class, splitting up class lines, further 
formatting them, organizing them into this tuple structure, and finally 
sorting the class tuples by name. From here, the class map was trivial 
as was the parent map. However, before anything else was printed, the 
structure of this class map attribute was checked for errors including 
all of the issues from PA4c. It was easier, and a little bit cleaner, 
to split off error checking from the rest of the code. If no errors 
were printed once that check was finished, the implementation map 
string was constructed. This was considerably more difficult as 
overriden methods had to be handled, and you couldn't just list them by 
inherited class as before. Additionally, type annotations had to be 
added here along with internal method information (which was more or 
less hard coded in).

At this point, it was time to do expression checking and generate the 
annotated AST. Things were done differently here, but they intersfaced 
well enough with the rest of the code. This was done by first getting 
three parts of the context from the class map, and reformatting them 
as Data.Map items to be passed around. All parts of each class were 
checked recursively and by expression type. All parts returned a tuple 
containing error information and parts of the annotated AST. If there 
was any error, it would propagate back to the beginning of the 
recursion. Special rules had to be considered for SELF_TYPE in new and 
case, and dispatch was conplicated, but with the use of those helper 
functions with methods from before, these issues were manageable. Most 
of the expressions were fairly straightforward to check in this manner 
by checking for errors and then checking sub-expressions.

One feature of the type checker made in this project which is
relatively uncommon is that it parses the abstract syntax tree as it
type checks. For this reason, all of the type checker functions pass
around lists of lines which both have been parsed and will be parsed.
The functions are designed so that the annotated abstract syntax tree
will just be completely done in the form of the parsed lines once a 
program is completely type checked. Although this method required a
double pass at certain times when the type of an expression is not
known from the start (e.g. case), but it had the overall benefit of 
making the annotation production trivial once it had been type checked.

Testing the assignment was when it became apparent that using a strongly,
statically typed language like Haskell was a good decision. Once the code
was able to pass the Haskell type-checker, we were pretty certain that
it at least did what we wanted it to. Then, the testing came down to two
different phases: an initial bulk testing phase, where it was tested against
the PA4t test suite and a special case testing phase, where we scoured the
cool reference manual for anything tricky that we may have missed. In the
first phase, the bulk testing primarily was done on one group member's
rosetta.cl assignment. Luckily, this file was extremely verbose to the 
point of being nearly 600 lines long, and it provided a good test of most
common features. For the special case testing phase, it involved searching
for lesser-known errors such as multiple case branches with the same type
or naming an attribute self and then testing those. Additionally in this
phase, multiple different configurations of a large number of classes were
used to check for errors in the recombination of class annotated ASTs to
the program annotated AST.

All in all, this was easily the most difficult assignment to crack so 
far. Partially, this was just due to the volume of work required, but 
it was also due to the fact that we didn't have lex or yacc on our side 
this time. With the interpreter posing a similar challenge to come, the
next assignment may prove to be even more difficult.
