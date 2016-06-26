# ------------------------------------------------------------
# main.py
#
# tokenizer for sespool
#
# ------------------------------------------------------------

import ply.lex as lex

# List of token names.   This is always required
tokens = (
    'A',
    'LET', 'EQUAL', 'BE', 'AS',
    'STORE', 'IN',
    'WHILE', 'IF', 'THEN', 'OTHERWISE',
    'GET', 'TAKE',
    'HAS', 'HAVE', 'DOES', "DOESN'T",
    'IS', "ISN'T",
    'AND', 'OR', 'NOT',
    'FINALLY',
    'CALLED,'
    'OWNERSHIP',
    'INTEGER',
    'WORD',
    'COMMA',
    'PERIOD',
    'INDENT',
    'SPACE',
    'NEWLINE'
)

# Regular expression rules for simple tokens
t_A             = r'A|a'
t_HAS           = r'(H|h)as'
t_AND           = r'(A|a)nd'
t_OR            = r'(O|o)r'
t_NOT           = r'(N|n)ot'
t_CALLED        = r'(C|c)alled'
t_DOTHEFOLLOWING= r'(D|d)o the following'
t_OWNERSHIP     = r'\'s'
t_WORD          = r'[a-z-]+'
t_COMMA         = r'\,(\s|\n)'
t_PERIOD        = r'\.(\s|\n)'
t_TAB           = r'\t'
t_SPACE         = r'\s'

# A regular expression rule with some action code
def t_INTEGER(t):
    r'\d+'
    t.value = int(t.value)    
    return t

def t_FLOAT(t):
    r'\d+\.\d'
    t.value = float(t.value)
    return t

# Define a rule so we can track line numbers
def t_NEWLINE(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

# A string containing ignored characters (spaces and tabs)
t_ignore  = ''

# Error handling rule
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

# Build the lexer
lexer = lex.lex()
# Test it out
source = '''
    A point has a number x and a number y. 
    A vector has a point called point-a and a point called point-b.
    To get a vector's length, do the following. Get the difference
between the vector's point-a's x and the vector's point-b's x
and store it in x-difference. Get the difference between the vector's 
point-a's y and the vector's point-b's y and store it in 
y-difference. Finally, get the square root of the sum of x-difference and
y-difference.
'''

# Give the lexer some input
source = source.lower()
lexer.input(source)

# Tokenize
while True:
    tok = lexer.token()
    if not tok: 
        break      # No more input
    print(tok)
