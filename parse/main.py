import lex
import yacc
from string import join
import sys

############################
# Cool AST Class Definitions
############################
class CoolASTObject(object):
    pass

#takes a CoolList of CoolClasses
class CoolAST(CoolASTObject):
    def __init__(self, class_list):
        self.class_list = class_list
    def __str__(self):
        return str(self.class_list)
        
#takes a list of CoolASTObjects
class CoolList(CoolASTObject):
    def __init__(self, items=[]):
        self.internal_list = items
    def add(self, item):
        self.internal_list.insert(0, item)
        return self
    def __str__(self):
        strings = [str(item) for item in self.internal_list]
        result = str(len(self.internal_list)) 
        if len(strings) > 0:
            result += '\n' + join(strings, '\n')
        return result
        
#takes a CoolID, a CoolList, and a CoolID(or None)
class CoolClass(CoolASTObject):
    def __init__(self, class_id, features, inherits=None):
        self.inheritance = None
        if inherits != None:
            self.inheritance = inherits
        self.class_id = class_id
        self.features = []
        self.features = features
    def add_feature(self, feature):
        self.features.append(feature)
    def __str__(self):
        result = str(self.class_id) 
        if self.inheritance is None:
            result = result + '\nno_inherits'
        else:
            result = result + '\ninherits\n' + str(self.inheritance)
        result = result + '\n' + str(self.features)
        return result

#takes an int and a string
class CoolID(CoolASTObject):
    def __init__(self, line, id_string):
        self.line = line
        self.id_string = id_string
    def __str__(self):
        return str(self.line) + '\n' + self.id_string
#helper function to make identifier and type creation easier
def ast_id(p, index):
    return CoolID(p.lineno(index), p[index])

#takes a string a CoolID, a CoolID, a CoolExpression (or None), 
#and a CoolList (or None)
class CoolFeature(CoolASTObject):
    def __init__(self, variety, name, cool_type, body=None, forms=None):
        self.variety = variety
        self.name = name
        self.cool_type = cool_type
        if variety is 'attribute_no_init':
            pass
        elif variety is 'attribute_init':
            self.initial = body
        elif variety is 'method':
            self.formals = forms
            self.body = body
    def __str__(self):
        result = self.variety
        if result is 'attribute_no_init':
            result += '\n' + str(self.name) 
            result += '\n' + str(self.cool_type)
        elif result is 'attribute_init':
            result += '\n' + str(self.name) 
            result += '\n' + str(self.cool_type)
            result += '\n' + str(self.initial)
        elif result is 'method':
            result += '\n' + str(self.name) 
            result += '\n' + str(self.formals)
            result += '\n' + str(self.cool_type)
            result += '\n' + str(self.body)
        return result

#takes a CoolID and a CoolID
class CoolFormal(CoolASTObject):
    def __init__(self, name, cool_type):
        self.name = name
        self.cool_type = cool_type
    def __str__(self):
        return str(self.name) + '\n' + str(self.cool_type)

#takes an int, a string, and args detailed in __init__ for each exp
class CoolExp(CoolASTObject):
    def __init__(self, line, exp_type, *args):
        self.line = line
        self.exp_type = exp_type
        #takes a CoolID and a CoolExp
        if self.exp_type is 'assign':
            self.variable = args[0]
            self.value_exp = args[1]
        #takes a CoolExp, a CoolID, and a CoolList of CoolExps
        elif self.exp_type is 'dynamic_dispatch':
            self.e = args[0]
            self.method = args[1]
            self.args = args[2]
        #takes a CoolExp, a CoolID, a CoolID, and a CoolList of CoolExps
        elif self.exp_type is 'static_dispatch':
            self.e = args[0]
            self.cool_type = args[1]
            self.method = args[2]
            self.args = args[3]
        #takes a CoolID and a CoolList of CoolExps
        elif self.exp_type is 'self_dispatch':
            self.method = args[0]
            self.args = args[1]
        #takes 3 CoolExps
        elif self.exp_type is 'if':
            self.pred = args[0]
            self.body = args[1]
            self.else_body = args[2]
        #takes 2 CoolExps
        elif self.exp_type is 'while':
            self.pred = args[0]
            self.body = args[1]
        #takes a CoolList of CoolExps
        elif self.exp_type is 'block':
            self.body = args[0]
        #takes a CoolID
        elif self.exp_type is 'new':
            self.class_type = args[0]
        #takes a CoolExp
        elif self.exp_type is 'isvoid':
            self.e = args[0]
        #takes a CoolExp
        elif self.exp_type is 'parens':
            self.e = args[0]
        #takes 2 CoolExps
        elif self.exp_type is 'plus':
            self.x = args[0]
            self.y = args[1]
        #takes 2 CoolExps
        elif self.exp_type is 'minus':
            self.x = args[0]
            self.y = args[1]
        #takes 2 CoolExps
        elif self.exp_type is 'times':
            self.x = args[0]
            self.y = args[1]
        #takes 2 CoolExps
        elif self.exp_type is 'divide':
            self.x = args[0]
            self.y = args[1]
        #takes 2 CoolExps
        elif self.exp_type is 'lt':
            self.x = args[0]
            self.y = args[1]
        #takes 2 CoolExps
        elif self.exp_type is 'le':
            self.x = args[0]
            self.y = args[1]
        #takes 2 CoolExps
        elif self.exp_type is 'eq':
            self.x = args[0]
            self.y = args[1]
        #takes a CoolExp
        elif self.exp_type is 'not':
            self.x = args[0]
        #takes a CoolExp
        elif self.exp_type is 'tilde':
            self.x = args[0]
        #takes an integer
        elif self.exp_type is 'integer':
            self.value = args[0]
        #takes a string
        elif self.exp_type is 'string':
            self.value = args[0]
        #takes a CoolID
        elif self.exp_type is 'identifier':
            self.variable = args[0]
        #takes nothing
        elif self.exp_type is 'true':
            pass
        #takes nothing
        elif self.exp_type is 'false':
            pass
    def __str__(self):
        result = str(self.line) + '\n' + self.exp_type
        #takes a CoolID and a CoolExp
        if self.exp_type is 'assign':
            result += '\n' + str(self.variable)
            result += '\n' + str(self.value_exp)
        #takes a CoolExp, a CoolID, and a CoolList of CoolExps
        elif self.exp_type is 'dynamic_dispatch':
            result += '\n' + str(self.e)
            result += '\n' + str(self.method)
            result += '\n' + str(self.args)
        #takes a CoolExp, a CoolID, a CoolID, and a CoolList of CoolExps
        elif self.exp_type is 'static_dispatch':
            result += '\n' + str(self.e)
            result += '\n' + str(self.cool_type)
            result += '\n' + str(self.method)
            result += '\n' + str(self.args)
        #takes a CoolID and a CoolList of CoolExps
        elif self.exp_type is 'self_dispatch':
            result += '\n' + str(self.method)
            result += '\n' + str(self.args)
        #takes 3 CoolExps
        elif self.exp_type is 'if':
            result += '\n' + str(self.pred)
            result += '\n' + str(self.body)
            result += '\n' + str(self.else_body)
        #takes 2 CoolExps
        elif self.exp_type is 'while':
            result += '\n' + str(self.pred)
            result += '\n' + str(self.body)
        #takes a CoolList of CoolExps
        elif self.exp_type is 'block':
            result += '\n' + str(self.body)
        #takes a CoolID
        elif self.exp_type is 'new':
            result += '\n' + str(self.class_type)
        #takes a CoolExp
        elif self.exp_type is 'isvoid':
            result += '\n' + str(self.e)
        #takes a CoolExp
        elif self.exp_type is 'parens':
            result = str(self.e)
        #takes 2 CoolExps
        elif self.exp_type is 'plus':
            result += '\n' + str(self.x)
            result += '\n' + str(self.y)
        #takes 2 CoolExps
        elif self.exp_type is 'minus':
            result += '\n' + str(self.x)
            result += '\n' + str(self.y)
        #takes 2 CoolExps
        elif self.exp_type is 'times':
            result += '\n' + str(self.x)
            result += '\n' + str(self.y)
        #takes 2 CoolExps
        elif self.exp_type is 'divide':
            result += '\n' + str(self.x)
            result += '\n' + str(self.y)
        #takes 2 CoolExps
        elif self.exp_type is 'lt':
            result += '\n' + str(self.x)
            result += '\n' + str(self.y)
        #takes 2 CoolExps
        elif self.exp_type is 'le':
            result += '\n' + str(self.x)
            result += '\n' + str(self.y)
        #takes 2 CoolExps
        elif self.exp_type is 'eq':
            result += '\n' + str(self.x)
            result += '\n' + str(self.y)
        #takes a CoolExp
        elif self.exp_type is 'not':
            result += '\n' + str(self.x)
        #takes a CoolExp
        elif self.exp_type is 'tilde':
            result = str(self.line) + '\nnegate'
            result += '\n' + str(self.x)
        #takes an integer
        elif self.exp_type is 'integer':
            result += '\n' + str(self.value)
        #takes a string
        elif self.exp_type is 'string':
            result += '\n' + str(self.value)
        #takes a CoolID
        elif self.exp_type is 'identifier':
            result += '\n' + str(self.variable)
        #takes nothing
        elif self.exp_type is 'true':
            pass
        #takes nothing
        elif self.exp_type is 'false':
            pass
        return result

#takes an int and a CoolList of CoolBindings
class CoolLetExp(CoolASTObject):
    def __init__(self, line, binding_list, body):
        self.line = line
        self.binding_list = binding_list
        self.body = body
    def __str__(self):
        result = str(self.line) + '\nlet' 
        result += '\n' + str(self.binding_list)
        result += '\n' + str(self.body)
        return result
        
#takes a CoolID, a CoolID, and a CoolExp (or None)
class CoolBinding(CoolASTObject):
    def __init__(self, variable, cool_type, value=None):
        self.variable = variable
        self.cool_type = cool_type
        self.value = value
    def __str__(self):
        result = ''
        if self.value is None:
            result += 'let_binding_no_init'
            result += '\n' + str(self.variable)
            result += '\n' + str(self.cool_type)
        else:
            result += 'let_binding_init'
            result += '\n' + str(self.variable)
            result += '\n' + str(self.cool_type)
            result += '\n' + str(self.value)
        return result

#takes an int, a CoolExp, and a CoolList of CoolCaseElems
class CoolCaseExp(CoolASTObject):
    def __init__(self, line, case_exp, case_elems):
        self.line = line
        self.case_exp = case_exp
        self.case_elems = case_elems
    def __str__(self):
        result = str(self.line) + '\ncase'
        result += '\n' + str(self.case_exp)
        result += '\n' + str(self.case_elems)
        return result

#takes a CoolId, a CoolID, and a CoolExp
class CoolCaseElem(CoolASTObject):
    def __init__(self, variable, cool_type, body):
        self.variable = variable
        self.cool_type = cool_type
        self.body = body
    def __str__(self):
        result = str(self.variable)
        result += '\n' + str(self.cool_type)
        result += '\n' + str(self.body)
        return result

######################################
# Terminal and precendence information
######################################
tokens = ['identifier','type','class','lbrace','rbrace','semi','lparen',
          'rparen','colon','dot','new','comma','inherits','larrow','at',
          'if','then','else','fi','while','loop','pool','isvoid','plus',
          'minus','times','divide','tilde','lt','le','equals','not',
          'integer','string','true','false','let','in','case','of',
          'esac','rarrow']
precedence = [
    ('left', 'in'),
    ('right', 'larrow'),
    ('left', 'not'),
    ('nonassoc', 'lt', 'le', 'equals'),
    ('left', 'plus', 'minus'),
    ('left', 'times', 'divide'),
    ('left', 'isvoid'),
    ('left', 'tilde'),
    ('left', 'at'),
    ('left', 'dot')
]

#############
# Dummy Lexer
#############
t_identifier = r".+"
def t_error(t):
    raise TypeError("Unknown text '%s'" % (t.value,))
lex.lex()

###############
# Parsing Rules
###############
def p_ast(p):
    "ast : class_list"
    p[0] = CoolAST(p[1])

def p_class_list(p):
    '''class_list : class_ast semi class_list
                  | class_ast semi'''
    if len(p) is 4:
        p[0] = p[3].add(p[1])  
    else: 
        p[0] = CoolList([p[1]])

def p_class_no_inherits_no_body(p):
    "class_ast : class type lbrace rbrace"
    p[0] = CoolClass(ast_id(p,2), CoolList())
def p_class_no_inherits(p):
    "class_ast : class type lbrace feature_list rbrace"
    p[0] = CoolClass(ast_id(p,2), p[4])
def p_class_inherits_no_body(p):
    "class_ast : class type inherits type lbrace rbrace"
    p[0] = CoolClass(ast_id(p,2), CoolList(), ast_id(p,4))
def p_class_inherits(p):
    "class_ast : class type inherits type lbrace feature_list rbrace"
    p[0] = CoolClass(ast_id(p,2), p[6], ast_id(p,4))
    
def p_feature_list(p):
    '''feature_list : feature semi feature_list
                    | feature semi'''
    if len(p) is 4:
        p[0] = p[3].add(p[1])  
    else: 
        p[0] = CoolList([p[1]])
    
def p_attribute_no_init(p):
    "feature : identifier colon type"
    p[0] = CoolFeature('attribute_no_init', 
                        ast_id(p,1), 
                        ast_id(p,3))
def p_attribute_init(p):
    "feature : identifier colon type larrow exp"
    p[0] = CoolFeature('attribute_init', 
                        ast_id(p,1), 
                        ast_id(p,3), 
                        p[5])
def p_feature_method(p):
    "feature : identifier lparen formal_list rparen colon type lbrace exp rbrace"
    p[0] = CoolFeature('method', 
                        ast_id(p,1), 
                        ast_id(p,6), 
                        p[8], 
                        p[3])
def p_feature_method_no_formals(p):
    "feature : identifier lparen rparen colon type lbrace exp rbrace"
    p[0] = CoolFeature('method', 
                        ast_id(p,1), 
                        ast_id(p,5), 
                        p[7], 
                        CoolList())

def p_formal_list(p):
    '''formal_list : formal comma formal_list
                   | formal'''
    if len(p) is 4:
        p[0] = p[3].add(p[1])  
    else:
        p[0] = CoolList([p[1]])
def p_formal(p):
    "formal : identifier colon type"
    p[0] = CoolFormal(ast_id(p,1), ast_id(p,3))
    
def p_exp_assign(p):
    "exp : identifier larrow exp"
    p[0] = CoolExp(p.lineno(1), 'assign', ast_id(p, 1), p[3])
def p_exp_dynamic_dispatch(p):
    '''exp : exp dot identifier lparen param_list rparen
           | exp dot identifier lparen rparen'''
    if len(p) is 7:
        p[0] = CoolExp(p[1].line, 
                       'dynamic_dispatch', 
                       p[1], 
                       ast_id(p,3), 
                       p[5])
    else:
        p[0] = CoolExp(p[1].line, 
                       'dynamic_dispatch', 
                       p[1], 
                       ast_id(p,3), 
                       CoolList())
def p_exp_static_dispatch(p):
    '''exp : exp at type dot identifier lparen param_list rparen
           | exp at type dot identifier lparen rparen'''
    if len(p) is 9:
        p[0] = CoolExp(p[1].line, 
                       'static_dispatch', 
                       p[1], 
                       ast_id(p,3), 
                       ast_id(p,5), 
                       p[7])
    else:
        p[0] = CoolExp(p[1].line, 
                       'static_dispatch', 
                       p[1], 
                       ast_id(p,3), 
                       ast_id(p,5), 
                       CoolList())
def p_exp_self_dispatch(p):
    '''exp : identifier lparen param_list rparen
           | identifier lparen rparen'''
    if len(p) is 5:
        p[0] = CoolExp(p.lineno(1), 
                       'self_dispatch', 
                       ast_id(p,1), 
                       p[3])
    else:
        p[0] = CoolExp(p.lineno(1), 
                       'self_dispatch', 
                       ast_id(p,1), 
                       CoolList())
def p_param_list(p):
    '''param_list : exp comma param_list
                  | exp'''
    if len(p) is 4:
        p[0] = p[3].add(p[1]) 
    else:
        p[0] = CoolList([p[1]])
def p_exp_if(p):
    "exp : if exp then exp else exp fi"
    p[0] = CoolExp(p.lineno(1), 'if', p[2], p[4], p[6])
def p_exp_while(p):
    "exp : while exp loop exp pool"
    p[0] = CoolExp(p.lineno(1), 'while', p[2], p[4])
def p_exp_block(p):
    "exp : lbrace exp_list rbrace"
    p[0] = CoolExp(p.lineno(1), 'block', p[2])
def p_exp_list(p):
    '''exp_list : exp semi exp_list
                | exp semi'''
    if len(p) is 4:
        p[0] = p[3].add(p[1])  
    else:
        p[0] = CoolList([p[1]])
def p_exp_let(p):
    "exp : let let_binding_list in exp"
    p[0] = CoolLetExp(p.lineno(1), p[2], p[4])
def p_let_binding_list(p):
    '''let_binding_list : let_binding comma let_binding_list
                        | let_binding'''
    p[0] = CoolList([p[1]]) if len(p) is 2 else p[3].add(p[1])
def p_let_binding(p):
    '''let_binding : identifier colon type
                   | identifier colon type larrow exp'''
    if len(p) is 6:
        p[0] = CoolBinding(ast_id(p,1), ast_id(p,3), p[5])
    else:
        p[0] = CoolBinding(ast_id(p,1), ast_id(p,3))
def p_exp_case(p):
    "exp : case exp of case_elements esac"
    p[0] = CoolCaseExp(p.lineno(1), p[2], p[4])
def p_case_elems(p):
    '''case_elements : case_element semi case_elements
                     | case_element semi'''
    p[0] = CoolList([p[1]]) if len(p) is 3 else p[3].add(p[1])
def p_case_elem(p):
    'case_element : identifier colon type rarrow exp'
    p[0] = CoolCaseElem(ast_id(p,1), ast_id(p,3), p[5])
def p_exp_new(p):
    "exp : new type"
    p[0] = CoolExp(p.lineno(1), 'new', ast_id(p,2))
def p_exp_isvoid(p):
    "exp : isvoid exp"
    p[0] = CoolExp(p.lineno(1), 'isvoid', p[2])
def p_exp_plus(p):
    "exp : exp plus exp"
    p[0] = CoolExp(p[1].line, 'plus', p[1], p[3])
def p_exp_minus(p):
    "exp : exp minus exp"
    p[0] = CoolExp(p[1].line, 'minus', p[1], p[3])
def p_exp_times(p):
    "exp : exp times exp"
    p[0] = CoolExp(p[1].line, 'times', p[1], p[3])
def p_exp_divide(p):
    "exp : exp divide exp"
    p[0] = CoolExp(p[1].line, 'divide', p[1], p[3])
def p_exp_tilde(p):
    "exp : tilde exp"
    p[0] = CoolExp(p.lineno(1), 'tilde', p[2])
def p_exp_lt(p):
    "exp : exp lt exp"
    p[0] = CoolExp(p[1].line, 'lt', p[1], p[3])
def p_exp_le(p):
    "exp : exp le exp"
    p[0] = CoolExp(p[1].line, 'le', p[1], p[3])
def p_exp_eq(p):
    "exp : exp equals exp"
    p[0] = CoolExp(p[1].line, 'eq', p[1], p[3])
def p_exp_not(p):
    "exp : not exp"
    p[0] = CoolExp(p.lineno(1), 'not', p[2])
def p_exp_parens(p):
    "exp : lparen exp rparen"
    p[2].line = p.lineno(1)
    p[0] = CoolExp(p.lineno(1), 'parens', p[2])
def p_exp_identifier(p):
    "exp : identifier"
    p[0] = CoolExp(p.lineno(1), 'identifier', ast_id(p,1))
def p_exp_integer(p):
    "exp : integer"
    p[0] = CoolExp(p.lineno(1), 'integer', p[1])
def p_exp_string(p):
    "exp : string"
    p[0] = CoolExp(p.lineno(1), 'string', p[1])
def p_exp_true(p):
    "exp : true"
    p[0] = CoolExp(p.lineno(1), 'true', p[1])
def p_exp_false(p):
    "exp : false"
    p[0] = CoolExp(p.lineno(1), 'false', p[1])

eof_line_no = 0
def p_error(p):
    if p:
        print "ERROR: %d: Parser: syntax error near %s"%(int(p.lineno), 
                                                         p.value)
        exit()
    else:
        print "ERROR: %d: Parser: unexpected EOF" % (eof_line_no)
        # never gets called?
        exit()
    
yacc.yacc()

###################################################
# Tokenizing function to use instead of lex.token()
###################################################
i = 0
tokenized_text = open(sys.argv[1], "r")
toks = tokenized_text.read().splitlines()
tokenized_text.close()
def my_token_func():
    global i, toks, eof_line_no
    if i >= len(toks):
        return None
    tok = lex.LexToken()
    tok.lineno = toks[i]
    eof_line_no = int(tok.lineno)
    tok.lexpos = 0
    i += 1
    tok.type = toks[i]
    if tok.type in ['type', 'identifier', 'integer', 'string']:
        i += 1
        tok.value = toks[i]
    else:
        tok.value = tok.type
    i += 1
    return tok    
    
# normalizes input for cross platform
def norm(tok):
    string.rstrip(tok, " \n\r")
    return string

# output ast
result_string = str(yacc.parse(tokenfunc=my_token_func))
outfile = sys.argv[1][:-3] + 'ast'
outfile_f = open(outfile, "w")
outfile_f.write(result_string)
outfile_f.close()
