
/* description: Parses and executes mathematical expressions. */
%{
var line = 1; //Need a variable to count lines
var comment_count = 0; //Need a variable to count nested comments NOTE: No longer a regular language
var output = "";//Accumulator for final lexer output, allows printing in case of no errors only
var error = false; //Variable to keep track of whether or not an error has occurred
var endfile = false; //Safety check for reaching EOF
%}

/* lexical grammar */


%lex

%x comment
%options flex

%%

<*>\n										{line++;} // Count lines in regular and comment mode
"(*"										{this.begin('comment'); comment_count++;}//Enter comment mode
<comment>"(*"								{comment_count++;}//Push on my comment-matching stack
<comment>"*)"								{comment_count--; if(comment_count==0) {this.begin('INITIAL');}}
<comment>.									/*Skip everything between in comments*/
<*>(\t|\r|\f|\v|' ')+                 	  	/* skip non-newline whitespace */
"--"(.|\t|\r|\f|\v|" ")*\n 					{line++;} // Account for single-line comments
"--"(.|\t|\r|\f|\v|" ")*$ 					// Account for single-line comments at end of file
//Now are the keyword matches. They come first so that they override the identifier/type rules.
"@"                   						{output = output.concat(line+"\nat\n");}
(c|C)(a|A)(s|S)(e|E)                		{output = output.concat(line+"\ncase\n");}
(c|C)(l|L)(a|A)(s|S)(s|S)                   {output = output.concat(line+"\nclass\n");}
":"                   						{output = output.concat(line+"\ncolon\n");}
","                   						{output = output.concat(line+"\ncomma\n");}
"/"                   						{output = output.concat(line+"\ndivide\n");}
"."                   						{output = output.concat(line+"\ndot\n");}
(e|E)(l|L)(s|S)(e|E)                   		{output = output.concat(line+"\nelse\n");}
"="								            {output = output.concat(line+"\nequals\n");}
(e|E)(s|S)(a|A)(c|C)                  		{output = output.concat(line+"\nesac\n");}
f(a|A)(l|L)(s|S)(e|E)                   	{output = output.concat(line+"\nfalse\n");}
(f|F)(i|I)									{output = output.concat(line+"\nfi\n");}
(i|I)(f|F)									{output = output.concat(line+"\nif\n");}
(i|I)(n|N)(h|H)(e|E)(r|R)(i|I)(t|T)(s|S)	{output = output.concat(line+"\ninherits\n");}
(i|I)(n|N)									{output = output.concat(line+"\nin\n");}
(i|I)(s|S)(v|V)(o|O)(i|I)(d|D)				{output = output.concat(line+"\nisvoid\n");}
"<-"										{output = output.concat(line+"\nlarrow\n");}
"{"											{output = output.concat(line+"\nlbrace\n");}
"}"											{output = output.concat(line+"\nrbrace\n");}
"<="										{output = output.concat(line+"\nle\n");}
(l|L)(e|E)(t|T)								{output = output.concat(line+"\nlet\n");}
(l|L)(o|O)(o|O)(p|P)						{output = output.concat(line+"\nloop\n");}
"("											{output = output.concat(line+"\nlparen\n");}
")"											{output = output.concat(line+"\nrparen\n");}
"<"											{output = output.concat(line+"\nlt\n");}
"-"											{output = output.concat(line+"\nminus\n");}
(n|N)(e|E)(w|W)								{output = output.concat(line+"\nnew\n");}
(n|N)(o|O)(t|T)								{output = output.concat(line+"\nnot\n");}
(o|O)(f|F)									{output = output.concat(line+"\nof\n");}
"+"											{output = output.concat(line+"\nplus\n");}
(p|P)(o|O)(o|O)(l|L)						{output = output.concat(line+"\npool\n");}
"=>"										{output = output.concat(line+"\nrarrow\n");}
";"											{output = output.concat(line+"\nsemi\n");}
(t|T)(h|H)(e|E)(n|N)						{output = output.concat(line+"\nthen\n");}
"~"											{output = output.concat(line+"\ntilde\n");}
"*"											{output = output.concat(line+"\ntimes\n");}
t(r|R)(u|U)(e|E)							{output = output.concat(line+"\ntrue\n");}
(w|W)(h|H)(i|I)(l|L)(e|E)					{output = output.concat(line+"\nwhile\n");}
//Here are three rules to handle identifiers, types, and integers
[a-z]([a-z]|[A-Z]|[0-9]|"_")*				{output = output.concat(line+"\nidentifier\n"+yytext+"\n");} //Matches identifiers
[A-Z]([a-z]|[A-Z]|[0-9]|"_")*				{output = output.concat(line+"\ntype\n"+yytext+"\n");} //Matches types
[0-9]+										%{//Code to recognize integers
												//Recognize the limit on Cool ints
												if(parseInt(yytext) <= 2147483647)
													output = output.concat(line+"\ninteger\n"+parseInt(yytext)+"\n");
												else
												{
													if(!endfile)
														console.log("ERROR: "+line+": Lexer: not a non-negative 32-bit signed integer: "+yytext);
												}
											%}
"\""("\\\""|[^\0"\""\n"\\"]|"\\"[^\0"\""\n])*"\""				%{//This regular expression accounts for strings by requiring 2 quotes and fitting all allowed characters in between.
																if((yytext.length > 1026) &&(!endfile))//Check max string length
																{
																	error = true;
																	console.log("ERROR: "+line+": Lexer: string constant is too long ("+(yytext.length-2)+" > 1024)");
																}
																else//Account for the string, remove quotes from lexeme
																	output = output.concat(line+"\nstring\n"+yytext.substring(1, yytext.length-1)+"\n");
															%}
<*><<EOF>>               					%{//Code for when the lexer reaches EOF
												if((comment_count > 0) && (!endfile))//Dis-allows EOF in comments
												{
													error = true;
													console.log("ERROR: "+line+": Lexer: EOF in (* comment *)");
												}
												if((!error) && (!endfile))//Only output if there is an error
												{
													require('fs').writeFileSync(process.argv[2].concat("-lex"), output);
													return 'EOF';
												}
												else
												{
													return 'EOF';
												}
											%}
.                     						%{//This section picks up any character which does not match the rules and reports it as an error.
												if(!error)
												{
													error = true;
													console.log("ERROR: "+line+": Lexer: invalid character: "+yytext);
												}
											%}

/lex

%%

A
	: A EOF
	|
	;

