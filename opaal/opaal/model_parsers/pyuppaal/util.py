# -*- coding: utf-8 -*-
### BEGIN LICENSE
# Copyright (C) 2010 Mads Chr. Olesen <mchro@cs.aau.dk>
#This program is free software: you can redistribute it and/or modify it 
#under the terms of the GNU General Public License version 3, as published 
#by the Free Software Foundation.
#
#This program is distributed in the hope that it will be useful, but 
#WITHOUT ANY WARRANTY; without even the implied warranties of 
#MERCHANTABILITY, SATISFACTORY QUALITY, or FITNESS FOR A PARTICULAR 
#PURPOSE.  See the GNU General Public License for more details.
#
#You should have received a copy of the GNU General Public License along 
#with this program.  If not, see <http://www.gnu.org/licenses/>.
### END LICENSE

from opaal import util
from pyuppaal.ulp import expressionParser, updateStatementParser
import pyuppaal
import ctypes

class PyuppaalError(util.Error):
    pass

class IllegalExpressionException(PyuppaalError):
    pass

def statement_str_to_python(statement):
    """Convert a statement to valid Python code.
    Very hackish."""
    replacements = {
        'true': 'True',
        'false': 'False',
        '&&': ' and ',
        ',': ' ; ',
    }
    for (s, r) in replacements.iteritems():
        statement = statement.replace(s, r)
    return statement


def expression_str_to_python(s, succgen=None):
    """Convert a string (expression) to valid Python code"""
    ast = expressionParser.parse_expression(s)
    return expression_to_python(ast, succgen)

binops = {
    'Plus': '+',
    'Minus': '-',
    'Times': '*',
    'Divide': '/',
    'Modulo': '%',
    'Greater': ' > ',
    'GreaterEqual': ' >= ',
    'Less': ' < ',
    'LessEqual': ' <= ',
    'Equal': ' == ',
    'Minus': ' - ',
    'NotEqual': ' != ',
}
def expression_to_python(node, succgen=None):
    """Convert an AST (of an expression) to valid Python code.
    @succgen is optional, if given will check that identifiers can be found.
    """
    if not node: #empty AST
        return ""
    if node.type == 'And':
        return expression_to_python(node.children[0], succgen) + \
            " and " + expression_to_python(node.children[1], succgen)
    elif node.type == 'Or':
        return expression_to_python(node.children[0], succgen) + \
            " or " + expression_to_python(node.children[1], succgen)
    elif node.type == 'BitAnd':
        return expression_to_python(node.children[0], succgen) + \
            " & " + expression_to_python(node.children[1], succgen)
    elif node.type == 'BitOr':
        return expression_to_python(node.children[0], succgen) + \
            " | " + expression_to_python(node.children[1], succgen)
    elif node.type == 'LeftShift':
        return expression_to_python(node.children[0], succgen) + \
            " << " + expression_to_python(node.children[1], succgen)
    elif node.type == 'UnaryNot' and len(node.children) == 1:
        return "not " + expression_to_python(node.children[0], succgen)
    elif node.type == 'UnaryMinus' and len(node.children) == 1:
        return "- " + expression_to_python(node.children[0], succgen)
    elif node.type in binops.keys():
        return expression_to_python(node.children[0], succgen) + \
            binops[node.type] + \
            expression_to_python(node.children[1], succgen)
    elif node.type == 'Number' and len(node.children) == 0:
        return str(node.leaf)
    elif node.type == 'True' and len(node.children) == 0:
        return "True"
    elif node.type == 'False' and len(node.children) == 0:
        return "False"
    elif node.type == 'Identifier' and len(node.children) == 1 and node.leaf == None:
        i_name = node.children[0]
        if succgen:
            if succgen.is_variable(i_name) or \
                i_name in [name for (name, _) in succgen.clocks]:
                return i_name
            elif i_name in ['True', 'False', 'INT_MAX', 'INT_MIN']:
                return i_name
            elif i_name in succgen.constants:
                return i_name
            else:
                print succgen.clocks
                print map(tuple, succgen.variables)
                raise IllegalExpressionException('Unknown identifier ' + i_name)
        else:
            return i_name
    elif node.type == 'Identifier' and (len(node.children) == 2 or node.leaf):

        #Of the form "Template."
        if succgen and node.children[0] in succgen.templatename_to_idx:
            t_idx = succgen.templatename_to_idx[node.children[0]]
            template = succgen.model.templates[t_idx]
            f_name = node.children[1].children[0]

            #case: Template.var | Template.clock
            #XXX this is incorrect
            if succgen.is_variable(f_name):
                return f_name
            if f_name in [name for (name, _) in succgen.clocks]:
                return f_name

            #case: Template.location
            for (loc_idx, loc) in enumerate(template.locations):
                if f_name == loc.name.value:
                    return "locs[%d] == %d" % (t_idx, loc_idx)
        #Of the form "variable.x" or "variable[x][x]...[x]"
        #if no succgen, assume its a variable
        elif not succgen or node.children[0] in [v[0] for v in succgen.variables] or \
                node.children[0] in [c[0] for c in succgen.clocks]:
            if len(node.children) == 2:
                #XXX, handle x.y.2?
                assert len(node.children) == 2
                return node.children[0] + "." + node.children[1].children[0]
            elif node.leaf:
                idxs = []
                for c in node.leaf.children:
                    assert c.type == 'Index'
                    idxs += [expression_to_python(c.leaf, succgen)]
                idxs = "".join(["[" + x + "]" for x in idxs])
                return node.children[0] + idxs
            else:
                raise IllegalExpressionException('Unknown construction ' + node + node.children + node.leaf)
        else:
            raise IllegalExpressionException('Unknown identifier ' + 
                node.children[0])

    elif node.type == 'FunctionCall':
        #collect full identifier
        ident = []
        def collect(x):
            assert x.type == 'Identifier'
            ident.append(x.children[0])
            return True
        node.children[0].visit(collect)
        ident = ".".join(ident)

        #collect parameters
        params = []
        for p in node.leaf:
            params.append(expression_to_python(p, succgen))
        params = ", ".join(params)

        return ident + "(" + params + ")"
        #XXX Assume of the form "variable.f()"
        #return node.children[0].leaf + "." + node.children[0].children[0].leaf + "()"
    elif node.type == 'Expression' and len(node.children) == 1:
        return expression_to_python(node.children[0], succgen)
    elif node.type == 'Initializer': #FIXME Currently a work around for the value analysis
        return "[]" 
    elif node.type == 'NodeTypedef' and node.children[0].type == 'TypeInt': #Hack to support typedefs in array declaration(BAwCC models)
        return expression_to_python(node.children[0].children[1], succgen)+"-"+expression_to_python(node.children[0].children[0], succgen)
    else:
        print node
        raise IllegalExpressionException('Illegal expression type: ' + 
            node.type)


def channame_str_to_index_cexprs(s, succgen=None):
    """Convert a string (channel name) to a pair (str, list) where the first
    element is the channel name, and the second element is a list of the 
    expressions comprising the indexes.
    Example: input "chan_name[N]"
            output ("chan_name", ["N"])
    Note that if the indexes can all be statically evaluated, they are returned
    in the channel name:
    Example: input "chan_name[3]"
            output ("chan_name[3]", [])
    """
    ast = expressionParser.parse_expression(s)
    return channame_to_index_cexprs(ast, succgen)

def channame_to_index_cexprs(node, succgen=None):
    """See channame_str_to_index_cexprs

    @succgen is optional, if given will check that identifiers can be found.
    """
    if not node: #empty AST
        return ("", [])

    #try evaluating statically, using Python
    (static, pythonexpr) = channame_to_python_format_string(node, succgen)
    if static:
        return (pythonexpr, [])

    #else: some indexes could not be evaluated, "channame[N]"
    if node.type == 'Identifier':
        #if no succgen, assume its a channel
        
        if not succgen or node.children[0] in succgen.channel_identifiers:
            
            if node.leaf: #Have IndexList?  Of the form "channame[x][x]...[x]"
                index_exprs = []
                if node.leaf.children[0].type == 'Index':
                    idxs = []
                    for c in node.leaf.children:
                        assert c.type == 'Index'
                        expr = expression_to_c(c.leaf, succgen)
                        idxs += [expr]
                    return (node.children[0], idxs)
                else:
                    raise IllegalExpressionException('Unknown construction ' + 
                            node.leaf + " with child of type " + node.children[0].type)
            else: #of the form "channame"
                return (node.children[0], [])
        else:
            raise IllegalExpressionException('Unknown channel ' + 
                node.children[0])
    else:
        raise IllegalExpressionException('Illegal expression type for channame: ' + 
            node.type)

def channame_str_to_python_format_string(s, succgen=None):
    """Convert a string (channel name) to a pair (bool, str) where the first
    element is whether the name is static (that is not dependent on the current
    state), and the second element is a Python format string which can be used
    together with a state to get the channel name.
    Example: input "chan_name[N]"
            output (False, "chan_name[%(N)s]")
            which can be used with a state "s" as such:
            "chan_name[%(N)s]" % s == "chan_name[5]"
    """
    ast = expressionParser.parse_expression(s)
    return channame_to_python_format_string(ast, succgen)


def _expression_to_python_format_string(node, succgen=None):
    """Convert an expression to a Python format string, evaluating as much as
    possible."""
    if node.type == 'And':
        assert False #XXX
        #return expression_to_python(node.children[0], succgen) + \
        #    " and " + expression_to_python(node.children[1], succgen)
    elif node.type == 'Or':
        assert False #XXX
        #return expression_to_python(node.children[0], succgen) + \
        #    " or " + expression_to_python(node.children[1], succgen)
    elif node.type in binops.keys():
        s1, e1 = _expression_to_python_format_string(node.children[0], succgen)
        s2, e2 = _expression_to_python_format_string(node.children[1], succgen)

        #both static? evaluate!
        comb_exp = e1 + binops[node.type] + e2
        if s1 and s2:
            return (True, str(eval(comb_exp)))
        else:
            return (False, comb_exp)
            
    elif node.type == 'Number' and len(node.children) == 0:
        return (True, str(node.leaf))
    elif node.type == 'Identifier' and len(node.children) == 1:
        i_name = node.children[0]
        if succgen:
            if i_name in succgen.constants:
                return (True, str(succgen.constants[i_name]))
            elif succgen.is_variable(node.children[0]):
                return (False, "%(" + i_name + ")s")
            raise IllegalExpressionException('Unknown identifier ' + i_name)
        else:
            return (False, "%(" + i_name + ")s")
    elif node.type == 'FunctionCall': #Used in the LTSmin branch
        return (False, "Func"+expression_to_c(node, succgen))
    else:
        print node
        raise IllegalExpressionException('Illegal expression type: ' + 
            node.type)

def channame_to_python_format_string(node, succgen=None):
    """See channame_str_to_python_format_string

    @succgen is optional, if given will check that identifiers can be found.
    """
    if not node: #empty AST
        return (True, "")

    if node.type == 'Identifier': # and len(node.children) >= 1:
        #if no succgen, assume its a channel
        if not succgen or node.children[0] in succgen.channel_identifiers:
            #Of the form "channame[x][x]...[x]"
            static = True
            if node.leaf: #Have IndexList?
                idxs = []
                for c in node.leaf.children:
                    assert c.type == 'Index'
                    (exprstatic, expr) = _expression_to_python_format_string(c.leaf, succgen)
                    static = static and exprstatic
                    idxs += [expr]
                idxs = "".join(["[" + x + "]" for x in idxs])
                return (static, node.children[0] + idxs)
            else:
                return (True, node.children[0])
        else:
            print node, succgen.channel_identifiers
            raise IllegalExpressionException('Unknown channel ' + 
                node.children[0])
    else:
        raise IllegalExpressionException('Illegal expression type for channame: ' + 
            node.type)


def statement_str_to_c(strstatement, succgen, sname="out"):
    """Convert a (string) statement to valid c code. """
    
    myparser = updateStatementParser.updateStatementParser(strstatement)
    ast = myparser.parseUpdateStatements()
    
    str_list = []
    clock_reset = []
    def statement_visit_gen(self):
        if self.type in ('RootNode', 'Assignment', 'Identifier', 'FunctionCall'):
            if self.type == 'RootNode':
                str_list.append("")
                for c in self.children:
                    c.visit(statement_visit_gen)
            else:
                visit_statement(str_list, self, succgen, 0, sname)

    ast.visit(statement_visit_gen)
    return ''.join(str_list)


def expression_str_to_c(strexpr, succgen=None, sname="in", clockexpr="true"):
    """Convert a string (expression) to valid c code"""
    ast = expressionParser.parse_expression(strexpr)
    return expression_to_c(ast, succgen, sname, clockexpr)

def expression_to_c(ast, succgen=None, sname="in", clockexpr="true"):
    visitor = ExpressionToCVisitor(succgen, sname, clockexpr)
    return visitor(ast)

class ClockExpressionException(Exception):
    pass

class ExpressionToCVisitor(object):
    def __init__(self, succgen=None, sname="in", clockexpr="true"):
        """Convert an AST (of an expression) to valid c code.
        @succgen is optional, if given will check that identifiers can be found.

        @clockexpressions determines the handling of expressions involving clocks.
        They are typically replaced by "true", as they should be handled differently.
        """
        self.succgen = succgen
        self.sname = sname
        self.clockexpr = clockexpr

    def __call__(self, *args, **kwargs):
         return self.visit(*args, **kwargs)

    def visit(self, node):
        if not node: #empty AST
            return ""
        elif node.type in binops.keys():
            try:
                return "("+ self.visit(node.children[0]) + \
                    binops[node.type] + \
                    self.visit(node.children[1]) + ")"
            except ClockExpressionException:
                return self.clockexpr
        elif node.type in clock_binops.keys():
            try:
                return self.visit(node.children[0]) + \
                        clock_binops[node.type] + \
                    self.visit(node.children[1])
            except ClockExpressionException:
                return self.clockexpr
        elif node.type in pre_unaryops.keys():
            return pre_unaryops[node.type] + self.visit(node.children[1])
        elif node.type in post_unaryops.keys():
            op_str = post_unaryops[node.type]
            return self.visit(node.children[0]) + op_str
        else:
            tocall = getattr(self, "visit_" + node.type)
            if tocall:
                return tocall(node)
        raise IllegalExpressionException('Illegal expression type: ' + 
            node.type)

    def visit_Index(self, node):
        return "[" + self.visit(node.leaf) + "]"

    def visit_And(self, node):
        return "(" + self.visit(node.children[0]) + \
            ") && (" + self.visit(node.children[1]) + ")"
    def visit_Or(self, node):
        return "(" + self.visit(node.children[0]) + \
            ") || (" + self.visit(node.children[1]) + ")"
    def visit_BitOr(self, node):
        return self.visit(node.children[0]) + \
            " | " + self.visit(node.children[1])
    def visit_BitAnd(self, node):
        return self.visit(node.children[0]) + \
            " & " + self.visit(node.children[1])
    def visit_LeftShift(self, node):
        return self.visit(node.children[0]) + \
            " << " + self.visit(node.children[1])
    def visit_RightShift(self, node):
        return self.visit(node.children[0]) + \
            " >> " + self.visit(node.children[1])
    def visit_UnaryNot(self, node):
        return "!(" + self.visit(node.children[0]) + ")"
    def visit_UnaryMinus(self, node):
        return "-(" + self.visit(node.children[0]) + ")"
    def visit_Number(self, node):
        return str(node.leaf)
    def visit_Conditional(self, node):
        return "(" + self.visit(node.children[0]) + " ? " + \
                self.visit(node.children[1]) + " : " + self.visit(node.children[2]) +")"

    def visit_True(self, node):
        return "true"
    def visit_False(self, node):
        return "false"
    def visit_ClockRate(self, node):
        raise ClockExpressionException

    def visit_Identifier(self, node, FuncCall = False):
        i_name = node.children[0]

        if self.succgen:
            if self.succgen.is_variable(i_name) or is_struct_ident(i_name, self.succgen.structs, self.succgen.pars.identifierTypeDict):
                if len(node.children) == 1 and is_struct_ident(i_name, self.succgen.structs, self.succgen.pars.identifierTypeDict) and FuncCall: # if identifier is a struct type and this is a function call generate: structvar1, structvar2, ...
                    vtype = self.succgen.pars.identifierTypeDict[i_name].leaf
                    vdimensions = [] #node.children #TODO add array support
                    svdeclList = getStructVarDeclInternal(i_name, None, vtype, vdimensions, self.succgen.structs, self.succgen.constants, i_name)
                    (var_list, _) = makeVariableList(svdeclList, False)
                    return ', '.join([visit_identifier([], pyuppaal.ulp.parser.Identifier(varName), self.succgen, 0, self.sname, True) for (varName,_) in var_list])
                elif len(node.children) == 2 and is_struct_ident(i_name, self.succgen.structs, self.succgen.pars.identifierTypeDict): #Complex struct identifier
                    return visit_identifier([], node, self.succgen, 0, self.sname, True) 
                else:
                    return visit_identifier([], node, self.succgen, 0, self.sname, True)
            elif i_name in [name for (name, _) in self.succgen.clocks]:
                raise ClockExpressionException
            elif i_name in ['true', 'false', 'INT_MAX', 'INT_MIN']:
                return i_name
            elif i_name in self.succgen.constants:
                return i_name
            else:
                print "Constants", self.succgen.constants
                print "Variables", map(tuple, self.succgen.variables)
                print "structs", self.succgen.simplyfied_struct_name
                print "FuncCall", FuncCall
                raise IllegalExpressionException('Unknown identifier ' + i_name)
        else:
            return i_name

    def visit_FunctionCall(self, node):
        #collect full identifier
        ident = []
        def collect(x):
            assert x.type == 'Identifier'
            ident.append(x.children[0])
            return True
        node.children[0].visit(collect)
        ident = ".".join(ident)

        #collect parameters
        if ident[0:4] == "dbm.": #XXX workaround that dbm func. should not have out as argument
            params = []
        else:
            params = [self.sname]
        for p in node.leaf:
            #TODO - avoid unneeded packinging in expression
            if p.type == 'Expression' and len(p.children) == 1:
               p = p.children[0]

            if p.type == 'Identifier':
                params.append(self.visit_Identifier(p, FuncCall=True))
            else:
                params.append(self.visit(p))
        params = ", ".join(params)

        return ident + "(" + params + ")"
        #XXX Assume of the form "variable.f()"
        #return node.children[0].leaf + "." + node.children[0].children[0].leaf + "()"

    def visit_Expression(self, node):
        try:
            return self.visit(node.children[0])
        except ClockExpressionException:
            return self.clockexpr

    def visit_BooleanExpression(self, node):
        return self.visit(node.children[0])
    
    def visit_Initializer(self, node):
        initializer = []
        initializer.append("{")
        
        for c in node.children:
            initializer.append(self.visit(c))
            initializer.append(", ")

        initializer.append("}")

        return "".join(initializer)

class ClockRateException(Exception):
    pass

def invariant_str_to_c(strexpr, succgen=None, sname="out"):
    """Convert a string (from an invariant) to valid C code.
    In general, this is a conjunction of expressions, but with side-effects
    (e.g. updating the dbm)"""
    ast = expressionParser.parse_expression(strexpr)
    visitor = InvariantToCVisitor(succgen, sname)
    return visitor(ast)

class InvariantToCVisitor(ExpressionToCVisitor):
    """Convert an invariant AST to valid C code.
    In general, this is a conjunction of expressions, but with side-effects
    (e.g. updating the dbm)"""

    def visit(self, node):
        if not node: #empty AST
            return ""
        elif node.type in clock_binops.keys():
            try:
                return self.visit(node.children[0]) + \
                        clock_binops[node.type] + \
                    self.visit(node.children[1])
            except ClockRateException:
                #clock rates handled elsewhere
                return ""
            except ClockExpressionException:
                return "(!(" + expression_to_fedupdate_c(node, self.succgen, self.sname) + ").isEmpty())"
        elif node.type in binops.keys():
            try:
                return "("+ self.visit(node.children[0]) + \
                    binops[node.type] + \
                    self.visit(node.children[1]) + ")"
            except ClockExpressionException:
                raise IllegalExpressionException("Clocks may not be used with %s" % (node.type))
        elif node.type in pre_unaryops.keys():
            return pre_unaryops[node.type] + self.visit(node.children[1])
        elif node.type in post_unaryops.keys():
            op_str = post_unaryops[node.type]
            return self.visit(node.children[0]) + op_str
        else:
            tocall = getattr(self, "visit_" + node.type)
            if tocall:
                return tocall(node)
        raise IllegalExpressionException('Illegal expression type: ' + 
            node.type)

    def visit_ClockRate(self, node):
        raise ClockRateException

class NotClockExpressionException(Exception):
    pass

def expression_str_to_fedupdate_c(strexpr, succgen=None, sname="out"):
    """Convert a string (expression) containing clock expressions to the
    corresponding federation update statement in C."""
    ast = expressionParser.parse_expression(strexpr)
    try:
        ret = expression_to_fedupdate_c(ast, succgen, sname)
        if ret:
            return ret + "; "
        return ""
    except NotClockExpressionException:
        return ""

clock_binops = {
    'Greater': ' > ',
    'GreaterEqual': ' >= ',
    'Less': ' < ',
    'LessEqual': ' <= ',
    'Equal': ' == ',
}

pre_unaryops = {
    'PlusPlusPre': '++',
    'MinusMinusPre': '--',
}

post_unaryops = {
    'PlusPlusPost': '++',
    'MinusMinusPost': '--',
}

def is_clock(ast_node, succgen):
    if ast_node.type == 'Identifier':
        if ast_node.children[0] in succgen.clock_indexes:
            return True

    return False

def getComplexIdentifier(node):
    if len(node.children) == 2:
        return node.children[0]+'_'+getComplexIdentifier(node.children[1])
    else:
        return node.children[0]
    
def expression_to_fedupdate_c(node, succgen=None, sname="out"):
    """Convert an AST (of an expression) containing clock expressions
    to the corresponding federation update statement in C.
    @succgen is optional, if given will check that identifiers can be found.
    Otherwise assumes all identifiers are clocks.
    """

    if len(node.children) > 1:
        if node.type not in ['And', 'Or'] and not is_clock(node.children[0], succgen) and not is_clock(node.children[1], succgen):
            raise NotClockExpressionException

    if not node: #empty AST
        raise NotClockExpressionException
    if node.type == 'And':
        lhs_notclock = False
        rhs_notclock = False
        lhs = ""
        rhs = ""
        try:
            lhs = expression_to_fedupdate_c(node.children[0], succgen, sname)
            if not lhs:
                lhs_notclock = True
        except NotClockExpressionException:
            lhs_notclock = True

        try:
            rhs = expression_to_fedupdate_c(node.children[1], succgen, sname)
            if not rhs:
                rhs_notclock = True
        except NotClockExpressionException:
            rhs_notclock = True

        return lhs+"; "+rhs
    if node.type == 'Or':
        #Only one side may be clock expression
        lhs_notclock = False
        rhs_notclock = False
        lhs = ""
        rhs = ""
        try:
            lhs = expression_to_fedupdate_c(node.children[0], succgen, sname)
            if not lhs:
                lhs_notclock = True
        except NotClockExpressionException:
            lhs_notclock = True
        try:
            rhs = expression_to_fedupdate_c(node.children[1], succgen, sname)
            if not rhs:
                rhs_notclock = True
        except NotClockExpressionException:
            rhs_notclock = True

        assert lhs_notclock or rhs_notclock, "Only one side of 'or' can involve clock expressions!"
        if lhs_notclock:
            return rhs
        elif rhs_notclock:
            return lhs

    elif node.type in ['NotEqual']:
        if is_clock(node.children[0], succgen):
            print "Left side of NotEqual is a clock"
            assert False #XXX not handled
        elif is_clock(node.children[1], succgen):
            print "Right side of NotEqual is a clock"
            assert False #XXX not handled
        else:
            return ""
    elif node.type == 'UnaryNot' and len(node.children) == 1:
        if is_clock(node.children[0], succgen):
            print "Child of UnaryNot is a clock"
            assert False #XXX not handled
        else:
            return ""
    elif node.type in clock_binops.keys():
        #is right side is clock and left side is not a clock?
        if is_clock(node.children[1], succgen) and not is_clock(node.children[0], succgen):
            print "Please move clock to the left side or add support for rearrangement of AST"
            assert False
        
        #is left side clock?
        if is_clock(node.children[0], succgen):
            
            #clock to clock
            if is_clock(node.children[1], succgen):
                clockident = node.children[0]
                clockident1 = node.children[1]

                cindex = succgen.clock_indexes.index(clockident.children[0])
                cindex2 = succgen.clock_indexes.index(clockident1.children[0])
                compare_expr = "0";
            else: #on
                clockident = node.children[0]
                exprnode = node.children[1]
                compare_expr = expression_to_c(exprnode, succgen, sname)

                cindex = succgen.clock_indexes.index(clockident.children[0])
                cindex2 = 0 #not comparing against clock = comparing against 0clock
        else:
            return ""

        if node.type == "Less":
            return "*(%s->fed) &= constraint_t(%d, %d, %s, true)" % (sname, cindex, cindex2, compare_expr)
        elif node.type == "Greater":
            return "*(%s->fed) &= constraint_t(%d, %d, -%s, true)" % (sname, cindex2, cindex, compare_expr)
        elif node.type == "GreaterEqual":
            return "*(%s->fed) &= constraint_t(%d, %d, -%s, false)" % (sname, cindex2, cindex, compare_expr)
        elif node.type == "LessEqual":
            return "*(%s->fed) &= constraint_t(%d, %d, %s, false)" % (sname, cindex, cindex2, compare_expr)
        elif node.type == "Equal":
            return "*(%s->fed) &= constraint_t(%d, %d, %s, false); " % (sname, cindex, cindex2, compare_expr) + \
                   "*(%s->fed) &= constraint_t(%d, %d, -%s, false)" % (sname, cindex2, cindex, compare_expr)

    elif node.type == 'Expression' and len(node.children) == 1:
        try:
            return expression_to_c(node.children[0], succgen, sname)
        except NotClockExpressionException:
            return ""
    elif node.type == 'Number' and len(node.children) == 0:
        try:
            return expression_to_c(node, succgen, sname)
        except NotClockExpressionException:
            return ""
    elif node.type == 'Identifier':
        try:
            return expression_to_c(node, succgen, sname)
        except NotClockExpressionException:
            return ""
    elif node.type == 'FunctionCall':         
        return "" #Should be ignored for fedupdates
    else:
        print node.visit()
        raise IllegalExpressionException('Illegal expression type: ' + 
            node.type)

def uppaalcfunc_to_cfunc(func_ast, succgen, constant_decl, func_variables_uninit, parameter_list):
    cfunc = []

    assert(func_ast.type == 'Function')
    node = func_ast
    cfunc.append('\n')
    # Translate Node('Function', children, (type, identifier, parameters)) to c
   
    func_variables = []
    for vdecl in func_variables_uninit:
        vdecl.c_initval = expression_to_c(vdecl.initval, succgen, sname="out") 
        func_variables.append(vdecl)

    simplified_vdecl = []

    for vdecl in func_variables:
        if is_struct_type(vdecl.vartype, succgen.structs):
            succgen.simplyfied_struct_name[vdecl.identifier] = vdecl.vartype
            simplified_vdecl.extend( getStructVarDecl(vdecl, succgen.structs, succgen.constants, vdecl.identifier))
        else:
            simplified_vdecl.append(vdecl)
    
    (_,var_parts) = makeVariableList(simplified_vdecl, True)
    variables_decl = ';\n'.join(var_parts)

    parameter_list.reverse()
    parameter_list.append('state_struct_t *out')
    parameter_list.reverse()

    if not is_primitive_type(node.basic_type):
        type_str = 'void'
        #succgen.func_ret_struct.append(node.leaf[1].children[0])
    else:
        type_str = type_to_str(node.basic_type)
        
    cfunc.append('inline ' + type_str + ' ' + node.leaf[1].children[0] + '(' +  \
            ', '.join(parameter_list) + ')\n{\n')
    cfunc.append(constant_decl)
    cfunc.append(variables_decl)
    cfunc.append(';\n')
    
    for s in node.children:
        visit_statement(cfunc, s, succgen, 1)

    cfunc.append('\n}\n')

    return ''.join(cfunc)

def visit_statement(cfunc, node, succgen, level, sname = 'out'):
    
    sname = 'out'
    succgen.last_typedef = False
    succgen.if_statement = False
    def statement_visit_gen(self):    
        
        if succgen.last_typedef:
            return

        if self.type in ('Assignment', 'Identifier'):
            if self.type == 'Assignment':
                if self.leaf:
                    if is_clock(self.leaf, succgen):
                        if [c for (c,_) in succgen.clocks if c == self.leaf.children[0]]:
                            cindex = succgen.clock_indexes.index(self.leaf.children[0])
                            cfunc.append(sname)
                            cfunc.append("->fed->updateValue(")
                            cfunc.append(str(cindex))
                            cfunc.append(", ")
                            self.children[0].visit(statement_visit_gen)
                            cfunc.append(")")
                    else:
                        if is_struct_ident(self.leaf.children[0], succgen.structs, succgen.pars.identifierTypeDict) and len(self.leaf.children) == 1: #should chek iden

                            if self.children[0].type == 'Expression' and self.children[0].children[0].type == 'FunctionCall':
                                self.children[0].visit(statement_visit_gen)
                                cfunc.append(';\n')

                            vname = self.leaf.children[0]
                            vdimensions = [] #self.leaf.children[0].leaf #TODO array support 
                            structType = succgen.simplyfied_struct_name[vname]

                            svdecl_list_target = getStructVarDeclInternal(vname, None, structType, vdimensions, succgen.structs, succgen.constants, prename = vname)
                            (var_list,_) = makeVariableList(svdecl_list_target, False)
                            target_var_list = [visit_identifier([], pyuppaal.ulp.parser.Identifier(varName), succgen, 0, sname, True) for (varName,_) in var_list]
                        
                            if self.children[0].type == 'Expression' and self.children[0].children[0].type == 'Identifier':
                                svname = self.children[0].children[0].children[0]
                                svdimensions = [] #TODO array support 
                                sstructType = succgen.simplyfied_struct_name[svname]
                                assert sstructType == structType 
                                
                                svdecl_list_source = getStructVarDeclInternal(svname, None, sstructType, svdimensions, succgen.structs, succgen.constants, prename = svname)
                                (var_list,_) = makeVariableList(svdecl_list_source, False)
                                source_var_list = [(visit_identifier([], pyuppaal.ulp.parser.Identifier(varName), succgen, 0, sname, True), True) for (varName,_) in var_list]
                            elif self.children[0].type == 'Expression' and self.children[0].children[0].type == 'FunctionCall':
                                svdecl_list_src = getStructVarDeclInternal(structType, None, structType, [], succgen.structs, succgen.constants, prename = structType)
                                (source_var_list, _) = makeVariableList(svdecl_list_src, False)
                            else:
                                print "Unsupported expression:", self.children
                                raise Exception("Unsupported expression")


                            for (target_var, (source_var,_)) in zip(target_var_list, source_var_list):
                                cfunc.append(target_var+' = '+source_var+';\n')
                            
                        else:
                            self.leaf.visit(statement_visit_gen)
                            cfunc.append(' = ')
                            self.children[0].visit(statement_visit_gen)
                else:        
                    self.children[0].visit(statement_visit_gen)
            else:
                visit_identifier(cfunc, self, succgen, level, sname)
        elif node.type == 'WhileLoop':
            visit_whileLoop(cfunc, node, succgen, level, sname)
        elif node.type == 'ForLoop':    
            visit_forLoop(cfunc, node, succgen, level, sname)
        elif node.type == 'DoWhileLoop':  
            visit_doWhileLoop(cfunc, node, succgen, level, sname)
        elif node.type in ['If', 'IfBodyStatements', 'ElseIfBodyStatements', 'ElseBodyStatements']:
            visit_if(cfunc, node, succgen, level, sname)
            succgen.if_statement = True
        elif node.type in ['VarDeclList']:
#        elif node.type in ['VarDecl', 'NodeTypedef']:
#            for c in node.children:
 #               visit_varDecl(cfunc, node, succgen, level, sname, node.leaf)
            if node.type == 'NodeTypedef':
                succgen.last_typedef = True
        else:
            if self.type == 'Expression' or self.type == 'FunctionCall':
                cfunc.append(expression_to_c(self, succgen, sname))
            elif self.type == 'Return':
                if len(self.leaf.children[0].children) == 1 and \
                    self.leaf.children[0].type == 'Identifier' and \
                    self.leaf.children[0].children[0] in succgen.simplyfied_struct_name.keys():
                        vname = self.leaf.children[0].children[0]
                        vdimensions = [] #self.leaf.children[0].leaf #TODO array support 
                        structType = succgen.simplyfied_struct_name[vname]
                        svdecl_list_src = getStructVarDeclInternal(vname, None, structType, vdimensions, succgen.structs, succgen.constants, prename = vname)
                        (var_list,_) = makeVariableList(svdecl_list_src, False)
                        source_var_list = [visit_identifier([], pyuppaal.ulp.parser.Identifier(varName), succgen, 0, sname, True) for (varName,_) in var_list]
                        
                        svdecl_list_target = getStructVarDeclInternal(structType, None, structType, [], succgen.structs, succgen.constants, prename = structType)
                        (target_var_list, _) = makeVariableList(svdecl_list_target, False)
                        
                        for ((target_var,_), source_var) in zip(target_var_list, source_var_list):
                            cfunc.append(target_var+' = '+source_var+';\n')
                        cfunc.append('return;\n')
               # elif self.leaf.type == 'Expression' and len(self.leaf.children) == 1 and \
               #     self.leaf.children[0].type == 'FunctionCall' and \
               #     self.leaf.children[0].children[0] <- name of function     in succgen.list_of_functions_returning_structs:
               #     
                else:
                    cfunc.append("return ")
                    cfunc.append(expression_to_c(self.leaf, succgen, sname))
            else:
                raise Exception('Unexcepted token type: ' + self.type)

    node.visit(statement_visit_gen)
    if not succgen.if_statement:
        cfunc.append(";\n")
    return ''.join(cfunc)

def visit_whileLoop(cfunc, node, succgen, level, sname):
    cfunc.append('\n')
    cfunc.append('\t'*level+'while (' + expression_to_c(node.leaf[0], succgen, sname) + ')\n{\n')
    for c in node.children:
        visit_statement(cfunc, c, succgen, level + 1)

    cfunc.append('\n}\n')

def visit_doWhileLoop(cfunc, node, succgen, level, sname):
    cfunc.append('\n')
    cfunc.append('\t'*level+'do \n{\n')
    for c in node.children:
        visit_statement(cfunc, c, succgen, level + 1)

    cfunc.append('\n} while (' + expression_to_c(node.leaf[0], succgen, sname) + ')\n')

def visit_forLoop(cfunc, node, succgen, level, sname):
    cfunc.append('\n')
    #Do not add var decl in node.leaf[0], will be added together with other var decl's
    cfunc.append('\t'*level+'for (')
    visit_statement(cfunc, node.leaf[0], succgen, 0) 
    cfunc.append(expression_to_c(node.leaf[1], succgen, sname) + ';')
    visit_statement(cfunc, node.leaf[2], succgen, 0)
    cfunc.pop()
    cfunc.append(')\n{\n')

    for c in node.children:
        visit_statement(cfunc, c, succgen, level + 1)

    cfunc.append('\n}\n')

def visit_if(cfunc, node, succgen, level, sname):
    cfunc.append('\n')
    
    if node.type == 'If':
        pass
    elif node.type == 'ElseIfBodyStatements':
        cfunc.append('\t'*level+'} else if (' + expression_to_c(node.leaf[0], succgen, sname) + ')\n{\n')
    elif node.type == 'IfBodyStatements':
        cfunc.append('\t'*level+'if (' + expression_to_c(node.leaf[0], succgen, sname) + ')\n{\n')
    else:
        cfunc.append('\t'*level+'} else\n{\n')

    for c in node.children:
        visit_statement(cfunc, c, succgen, level + 1)

    if node.type == 'If':
        cfunc.append('\n}\n')

def visit_identifier(cfunc, node, succgen, level, sname = 'out', stroutput = False):
    
    if node.children[0] in [name for (name, _, _, _) in succgen.discrete_variables]:
        cfunc.append(sname)
        cfunc.append("->")
        cfunc.append(node.children[0])
    elif succgen.is_lattice_variable(node.children[0]):
        cfunc.append("(*")
        cfunc.append(sname)
        cfunc.append("->")
        cfunc.append(node.children[0])
        cfunc.append(")")
    elif len(node.children) == 2: #complex
        #TODo lookup
        complexName = getComplexIdentifier(node)
        if [True for (x,_,_,_) in succgen.discrete_variables if complexName == x]:
            cfunc.append(sname)
            cfunc.append("->")
        cfunc.append(complexName)
    else:
        cfunc.append(node.children[0])

    if node.leaf:
       # == 'IndexList':
        for c in node.leaf.children:
            if c.type == 'Index':
                cfunc.append("[")
                cfunc.append(expression_to_c(c.leaf, succgen, sname))
                cfunc.append("]")

    if stroutput:
        return ''.join(cfunc)
            
def visit_varDecl(cfunc, node, succgen, level, sname):
    #ignore will be generated from succgen.variables
    return

def type_to_str(type_str, unsigned=True):
    if type_str == 'TypeInt':
        if unsigned:
            return 'uint32_t'
        else:
            return 'int32_t'
    elif type_str == 'TypeConstInt':
        if unsigned:
            return 'const uint32_t'
        else:
            return 'const int32_t'
    elif type_str == 'TypeIntReference':
        if unsigned:
            return 'uint32_t&'
        else:
            return 'int32_t&'
    elif type_str == 'TypeBool':  
        return 'uint32_t'
    elif type_str == 'TypeConstBool':
        return 'const uint32_t'
    elif type_str == 'TypeVoid':
        return 'void'
    raise IllegalExpressionException('Illegal type: ' + type_str)

def vardecl_to_ctype(vdecl):
    type_str = vdecl.basic_type
    if is_primitive_type(type_str):
        unsigned = (vdecl.eval_range_min >= 0)
        return type_to_str(type_str, unsigned)
    else:
        print "vardecl_to_ctype", vdecl.identifier, vdecl.vartype #, is_struct_type(vdecl.basic_type)
        return "uint32_t" #FIXME we should resolve basic type or support nested struct's

def is_struct_ident(varName, structDict, identifierTypedef):
    try:
        varType = identifierTypedef[varName]
        return is_struct_type(varType.leaf, structDict)
    except:
        return False

def is_struct_type(varType, structDict):
    try:
        structDict[varType]
        return True
    except:
        return False

def is_primitive_type(type_str):
    primitive_type = ['TypeInt', 'TypeConstInt', 'TypeIntPointer', 'TypeBool', 'TypeConstBool', 'TypeBoolPointer', 'TypeVoid']

    if type_str in primitive_type:
        return True

    return False


def is_local(var, succgen):
    if var in [var_name for (var_name,_,_,_) in succgen.local_variables]:
        return True
    else: 
        return False

CTYPE_TO_CTYPES_TYPE = {
    "uint32_t": ctypes.c_uint32,
    "int32_t": ctypes.c_int32,
    "const uint32_t": ctypes.c_uint32,
    "const int32_t": ctypes.c_int32,
}


"""
The method should only be called with a vdecl of a struct type. For such a
vdecl the method will return a list of vdecl's of primitive types. This is true
also for nested structs.
"""
def getStructVarDecl(vdecl, structs, constants, prename = ''):
    return getStructVarDeclInternal(vdecl.identifier, vdecl.initval, vdecl.vartype, vdecl.array_dimensions, structs, constants, prename)


def getStructVarDeclInternal(vname, vinitval, vtype, vdimensions, structs, constants, prename = ''):
    assert structs[vtype] != None
    
    vdecl_list = []

    if prename == '':
        nested_name = vname 
    else:
        nested_name = prename+'_'+vname

    if vinitval:
        depth = len(vdimensions)
        result = []

        def find_struct_initializers(current_level, inode):
            if current_level == depth:
                result.extend(inode.children)
            else:
                for c in inode.children:
                    find_struct_initializers(current_level+1, c)

        find_struct_initializers(0, vinitval)
        sinit_list = result

        if depth == 0:
            initval_list = sinit_list
        else:
            initval_list = []
            for k in range(len(structs[vtype])):
                initval_list.append( pyuppaal.ulp.parser.Node('Initializer', children=sinit_list[k::len(structs[vtype])]) )
            
    else:
        initval_list = [None] * len(structs[vtype])

    for (svdecl, initvalue) in zip(structs[vtype], initval_list):
        varName = svdecl.identifier if prename == '' else prename + '_' + svdecl.identifier

        if not is_struct_type(svdecl.vartype, structs):
            nvdecl = pyuppaal.ulp.parser.VarDecl(varName, pyuppaal.ulp.parser.Node(svdecl.vartype), array_dimensions=vdimensions, initval=initvalue)
            eval_vardecl_expressions(nvdecl, constants, do_eval_initval=True)
            vdecl_list.append(nvdecl)
        else:     
            svdecl.initval = initval.children
            nested_vdecl_list = getStructVarDeclInternal(svdecl, structs, constants, nested_name)
            vdecl_list.extend(nested_vdecl_list)

    return vdecl_list




"""
If structs is not set constants and prename does not have any effect
"""
def makeVariableList(variables, local = False, thread_local = False): 
    var_list = []
    parts = []

    for vdecl in variables:
        if vdecl.vartype == 'TypeClock':
            continue
        
        var = vdecl.identifier 
        vtype = vardecl_to_ctype(vdecl)
        #For now this check is disabled to allow generating var lists for typedefs that just redefines int/bool 
        #if vdecl.type not in ['TypeInt', 'TypeBool']:  
        #    raise Exception("Incorrect type for makeVariableList iden:%s and type:%s" % (vdecl.identifier, vdecl.type))

        array_dimensions = vdecl.eval_dimensions
        #either use the valuated initval if possible, or use the c expression
        initval = None
        if not vdecl.eval_initval is None:
            initval = vdecl.eval_initval
        elif hasattr(vdecl, "c_initval"):
            initval = vdecl.c_initval
        if not initval:
            initval = "0"
        
        tmp_vtype = vtype 
        if thread_local == True:
            tmp_vtype = '__thread ' + vtype

        if array_dimensions == []:
            gen_array_dimensions = "";
            

            if local:
                parts += ["\t%s %s%s = %s" % (tmp_vtype, var, gen_array_dimensions, initval)]
            else:
                parts += ["\t%s %s%s" % (tmp_vtype, var, gen_array_dimensions)]
            
            var_list += [(var, CTYPE_TO_CTYPES_TYPE[vtype])]
        else:
            asize = 0
            gen_array_dimensions = "".join(map(lambda dim: '['+str(dim)+']', array_dimensions));
            for dim in array_dimensions:
                if asize == 0:
                    asize = dim
                else: 
                    asize = asize*dim
            var_list += [(var, CTYPE_TO_CTYPES_TYPE[vtype]*asize)]
            parts += ["\t%s %s%s" % (tmp_vtype, var, gen_array_dimensions)]

    return (var_list, parts)

def get_struct_member_vardecl(struct_type, member_name, declvisitor=None):
    """Return the type for the member @member_name, of the struct type defined by
    @struct_type."""
    for vardecllist in struct_type.children:
        assert vardecllist.type == "VarDeclList"
        for vardecl in vardecllist.children:
            assert vardecl.type == "VarDecl"
            ident = vardecl.identifier
            assert ident.type == "Identifier"
            ident_name = ident.children[0]
            if ident_name == member_name:
                return vardecl
                #return vardecllist.vartype
    return None

def _min_max(a, b):
    """Helper for @range_for_expression."""
    return (min(a[0], b[0]), max(a[1], b[1]))

def range_for_expression(node, declvisitor=None, constants=None):
    """Analyse an AST (of an expression) and return the (minimum, maximum)
    value range for it.
    @declvisitor is optional, if given will use declared type-range information
    @constants is optional, if given will look up constant values
    """
    if not node: #empty AST
        return (0,0)
    if node.type in ('And', 'Or'):
        return _min_max(
                range_for_expression(node.children[0], declvisitor, constants),
                range_for_expression(node.children[1], declvisitor, constants))
    elif node.type == 'UnaryMinus' and len(node.children) == 1:
        a = range_for_expression(node.children[0], declvisitor, constants)
        return (-a[1], -a[0])
    elif node.type == "Plus":
        a = range_for_expression(node.children[0], declvisitor, constants)
        b = range_for_expression(node.children[1], declvisitor, constants)
        return (a[0] + b[0], a[1] + b[1])
    elif node.type == "Minus":
        a = range_for_expression(node.children[0], declvisitor, constants)
        b = range_for_expression(node.children[1], declvisitor, constants)
        return (a[0] - b[1], a[1] - b[0])
    elif node.type == 'Number' and len(node.children) == 0:
        return (node.leaf, node.leaf)
    elif node.type == 'Identifier' and len(node.children) == 1:
        #indexlist = node.leaf # index'es can be ignored, array has same range for all elements
        i_name = node.children[0]
        if declvisitor:
            vdecl = declvisitor.get_vardecl(i_name)
            if vdecl:
                vdecl.eval_range_min = eval(expression_to_python(vdecl.range_min), {}, constants)
                vdecl.eval_range_max = eval(expression_to_python(vdecl.range_max), {}, constants)

                return (vdecl.eval_range_min, vdecl.eval_range_max)
            elif i_name in constants:
                return (constants[i_name], constants[i_name])
            raise IllegalExpressionException('Unknown identifier ' + i_name)
        else:
            #default int range
            return (-32767, 32767)
    elif node.type == 'Identifier' and len(node.children) == 2:
        #node.visit()
        #Of the form "variable.x" or "variable[x].y"
        #if no succgen, assume its a variable
        i_name = node.children[0]
        member_ident = node.children[1]
        member_name = member_ident.children[0]
        assert len(member_ident.children) == 1, "Nested struct access not supported in clock expressions (bytesize bug)"
        if declvisitor:
            vdecl = declvisitor.get_vardecl(i_name)
            if vdecl:
                #can ignore array indexes, as all items have same bounds
                vartype = declvisitor.parser.globalIdentifierTypeDict[i_name]
                c_vdecl = get_struct_member_vardecl(vartype, member_name)

                c_vdecl.eval_range_min = eval(expression_to_python(c_vdecl.range_min), {}, constants)
                c_vdecl.eval_range_max = eval(expression_to_python(c_vdecl.range_max), {}, constants)
                return (c_vdecl.eval_range_min, c_vdecl.eval_range_max)

            raise IllegalExpressionException('Unknown identifier ' + i_name)
        else:
            #default int range
            return (-32767, 32767)

    #elif node.type == 'FunctionCall':
    #XXX, look at return type
    elif node.type == 'Expression' and len(node.children) == 1:
        return range_for_expression(node.children[0], declvisitor, constants)
    else:
        raise IllegalExpressionException('Illegal expression type: ' + 
            node.type)

def eval_vardecl_expressions(vdecl, constants, do_eval_initval=True):
    """
    Evaluate the AST for the various properties of a VarDecl, e.g. 
    array_dimensions to eval_dimensions, initval to eval_initval, etc.

    @constants: dict of constants to use
    """
    (vident, vtype, vdimensions, initval) = vdecl
    #evaluate array dimensions to values
    vdecl.eval_dimensions = []
    for (dim_idx, dim) in enumerate(vdimensions):
        vdecl.eval_dimensions.append(eval(expression_to_python(dim), {}, constants))

    #evaluate initval to value
    vdecl.eval_initval = None
    if initval and do_eval_initval:
        if len(vdecl.eval_dimensions) == 0:
            vdecl.eval_initval = eval(expression_to_python(initval), {}, constants)
        else:
            vdecl.eval_initval = init_array(initval, vdecl.eval_dimensions, constants)

    #evaluate ranges to values
    vdecl.eval_range_min = None; vdecl.eval_range_max = None
    if vdecl.range_min:
        vdecl.eval_range_min = eval(expression_to_python(vdecl.range_min), {}, constants)
    if vdecl.range_max:
        vdecl.eval_range_max = eval(expression_to_python(vdecl.range_max), {}, constants)

def init_array_initializer(initializer, constants):
    parts=[]
    parts.append("{")
    for c in initializer.children:
        if c.type in ('Number', 'Expression', 'Identifier'):
            parts.append(str(eval(expression_to_python(c), {}, constants)))
        elif c.type in ('False', 'True', ):
            parts.append(c.type.lower())
        elif len(c.children) != 0:
            parts.extend(init_array_initializer(c, constants))
        else:
            raise IllegalExpressionException('Illegal initializer type: ' + 
                c.type)
        parts.append(", ")
    
    parts.append("}")
    return parts

def init_array_zero(array_dim):
    parts=[]
    parts += ["\t{ "]                        
    if len(array_dim) != 1:
        for i in range(array_dim[0]):
            parts.extend( init_array_zero(array_dim[1:len(array_dim)]) )
            parts += [","]
    else:
        parts += ["\t0,\n" * (array_dim[0]-1)]
        parts += ["\t0\n"]
    parts += ["\t}\n"]
    parts += '\t'
    return parts


def init_array(initval, eval_dimensions, constants):

    if initval is not None:
        return ''.join(init_array_initializer(initval, constants))
    else:
        return ''.join(init_array_zero(eval_dimensions))

# vim:ts=4:sw=4:expandtab
