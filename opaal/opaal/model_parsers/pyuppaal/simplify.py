#!/usr/bin/python
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
import pyuppaal
from pyuppaal.ulp import lexer, parser, systemdec_parser, selectStatementParser
import util
import copy
import re
import opaal.util
import itertools

class SimplifyModel:

    def __init__(self, nta, constant_overrides=dict()):
        self.nta = nta
        self.constant_overrides = constant_overrides
        self.parse_and_calculate_constants()

    def parse_and_calculate_constants(self):
        self.lex = lexer.lexer
        try:
            self.pars = parser.Parser(self.nta.declaration, self.lex)
        except Exception:
            opaal.util.emergencyExitUppaalCParser("Error parsing the model for calculating constants.")
        self.declvisitor = parser.DeclVisitor(self.pars)
        self.declvisitor.visit(self.pars.AST)
        
        self.constants = {}
        #constant overrides
        for (cident, cval) in self.constant_overrides.iteritems():
            #XXX assumes expression is already python
            self.constants[cident] = eval(cval, {}, self.constants)
        #evaluate constants to values
        for (cident, cval) in self.declvisitor.constants.iteritems():
            if not cident in self.constants:
                self.constants[cident] = eval(util.expression_to_python(cval), {}, self.constants)

    def simplify(self):
        self.expand_system_declaration()
        self.expand_selects()
        return self.nta

    def expand_selects(self):
        """Expand transitions with select based on the possible values for the 
        select variables."""
        for temp in self.nta.templates:
            new_transitions = []
            for trans in temp.transitions:
                if trans.select.value:
                    pars = selectStatementParser.selectStatementParser(trans.select.value, None, self.pars.typedefDict)
                    AST = pars.parseSelectStatements()
                    keys = []
                    values = []

                    for n in AST.children:
                        iden = n.type.children[0]
                        someType = n.children
                        keys.append(iden)
                        lower, upper = self.bounds_for_type(someType)
                        values.append(range(lower, upper+1))

                    for items in itertools.product(*values):
                        new_trans = copy.copy(trans)
                        new_trans.select.value = ''
                        for (ident, x) in zip(keys, items):
                            self.inline_var_in_trans(new_trans, ident, x)
                        
                        #can the truth value of guard be statically determined?
                        guardtautology = None
                        try:
                            if new_trans.guard.value.strip() != "":
                                guardtautology = eval(util.expression_str_to_python(new_trans.guard.value), {}, self.constants)
                        except NameError:
                            #expression uses variables
                           pass
                        if guardtautology == True:
                            new_trans.guard.value = ""
                        elif guardtautology == False:
                            #discard transition
                            continue
                        new_transitions.append(new_trans)
            temp.transitions = [t for t in temp.transitions if not t.select.value] + new_transitions
                    

    def bounds_for_type(self, someType):    
        if someType.type == 'NodeTypedef':
            someType = someType.children[0]

        assert someType.type == 'TypeInt' #TODO other types
        lowerexpr = util.expression_to_python(someType.children[0].children[0])
        upperexpr = util.expression_to_python(someType.children[1].children[0])

        lower = eval(lowerexpr, {}, self.constants)
        upper = eval(upperexpr, {}, self.constants)

        return (lower, upper)


    def expand_system_declaration(self):
        """Expand the model according to the system declaration:
        * For each automaton in the system create a unique template, 
          converting parameters to local variables.
        * Promote local variables to uniquely named global vars.
        """
        nta = self.nta
        ret = pyuppaal.NTA(declaration=nta.declaration)

        try:
            parser = systemdec_parser.SystemDeclarationParser(nta.system)
            res = parser.AST
        except Exception:
            opaal.util.emergencyExitSytemDecl("In the simplyfication phase a parsing error occurred when the system declaration in your model was being parsed.")
        #res.visit()

        # Instantiate process assignments
        for c in res.children:
            if c.type == 'ProcessAssignment':
                ident = c.leaf.children[0]
                tname = c.children[0].leaf.children[0]
                try:
                    template = [t for t in nta.templates if t.name == tname][0]
                except IndexError:
                    raise util.PyuppaalError("Template '%s' for instantiating '%s' not found!" % (tname, ident))
                inst_parameters = c.children[0].children

                #XXX copy over logic for implicit instantiation below on when to inline and when to convert
                #(convert'ing will fail for e.g. train-gate because of mis-parsing the sync's)
                formal_parameters = [p.strip() for p in template.parameter.split(',')]
                formal_parameter_idents = []
                for p in formal_parameters:
                    if p:
                        pident = p.split(' ')[-1]
                        formal_parameter_idents += [pident]

                if len(inst_parameters) != len(formal_parameter_idents):
                    raise util.PyuppaalError("Incorrect number of parameters for template '%s' for instantiating '%s'" % (tname, ident))

                if len(inst_parameters) == 0:
                    instantiated_template = copy.deepcopy(template)
                else:
                    #make parameters local variables
                    instantiated_template = copy.deepcopy(template)
                    for (formal_param, pnode) in zip(formal_parameters, 
                            inst_parameters):
                        instantiated_template.declaration = formal_param + " = " + \
                            str(eval(util.expression_to_python(pnode), {}, self.constants)) + ";\n" + \
                                instantiated_template.declaration
                instantiated_template.parameter = ''
                instantiated_template.name = ident

                #add to templates
                nta.templates += [instantiated_template]


        systemsnode = [c for c in res.children if c.type == 'System'][0]
        #systemsnode.visit()
        #print nta.templates
        
        retsystems = []
        prevprio = -1
        for inst in systemsnode.children:
            prio = inst.priority
            ident = inst.leaf
            tname = ident.children[0]

            temp = [t for t in nta.templates if t.name == tname][0]
            if prevprio == -1: #first process
                separator = ""
            else:
                separator = (prio != prevprio) and " < " or ", "
            prevprio = prio
            #case with no pars
            if temp.parameter.strip() == '':
                self.add_template_promote_local_vars(ret, temp)
                retsystems += [separator, temp.name]
            #case where we instantiate based on possible parameter values
            else:
                comb_temps = [copy.deepcopy(temp)]
                comb_temps[0].parameter = ''
                for par in [p.strip() for p in temp.parameter.split(',')]:
                    par_parts = par.split(' ')
                    if len(par_parts) == 2:
                        (constness, typename, ident) = ("", par_parts[0], par_parts[1])
                    else:
                        (constness, typename, ident) = par_parts
                    someType = self.pars.getType(typename)
                    lower, upper = self.bounds_for_type(someType.children[0])
                    
                    new_temps = []
                    for oldtemp in comb_temps:
                        for x in range(lower, upper+1):
                            if constness:
                                #inline const parameters
                                new_temp = self.inline_var_in_temp(oldtemp, ident, x)
                                new_temp.name += '_' + str(x)
                                new_temps += [new_temp]
                            else:
                                #make variable parameters local vars
                                new_temp = copy.deepcopy(oldtemp)
                                new_temp.declaration = constness + " " + typename + " " + ident + " = " + str(x) + ";\n" + \
                                    new_temp.declaration
                                new_temp.name += '_' + str(x)
                                new_temps += [new_temp]
                    comb_temps = new_temps
                for temp in comb_temps:
                    self.add_template_promote_local_vars(ret, temp)
                    retsystems += [separator, temp.name]
                    separator = ", "
            #TODO other cases
        ret.system = "system " + "".join(retsystems) + ";"
        self.nta = ret

    def add_template_promote_local_vars(self, nta, temp):
        """Add the template @temp to the nta @nta, promoting local variables
        to uniquely named global variables in the process."""
        lex = lexer.lexer
        try:
            pars = parser.Parser(temp.declaration, lex, typedefDict=self.pars.typedefDict)
        except Exception:
            opaal.util.emergencyExitUppaalCParser("Error parsing template declarations.")

        declvisitor = parser.DeclVisitor(pars)
        declvisitor.visit(pars.AST)

        for (c, _) in declvisitor.clocks:
            newident = "%s_%s" % (temp.name, c)
            assert declvisitor.get_type(newident) == None
            self.rename_var_in_temp(temp, c, newident)
        for (varname, _, _, _) in declvisitor.variables:
            newident = "%s_%s" % (temp.name, varname)
            assert declvisitor.get_type(newident) == None
            self.rename_var_in_temp(temp, varname, newident)
        for const in declvisitor.constants:
            newident = "%s_%s" % (temp.name, const)
            assert declvisitor.get_type(newident) == None
            self.rename_var_in_temp(temp, const, newident)
        for func_ast in declvisitor.functions:
            oldident = func_ast.leaf[1].children[0]
            newident = "%s_%s" % (temp.name, oldident)
            assert declvisitor.get_type(newident) == None
            self.rename_var_in_temp(temp, oldident, newident)

        nta.declaration += "\n/******** Declarations for %s ********/\n%s\n" % (temp.name, temp.declaration)
        temp.declaration = ""
        nta.templates += [temp]

    def rename_var_in_temp(self, temp, oldident, newident):
        """Returns a new template, with oldident renamed to newident."""
        regex = re.compile('(?<!\w)%s(?!\w)' % oldident)
        temp.declaration = re.sub(regex, str(newident), temp.declaration)
        for trans in temp.transitions:
            self.inline_var_in_trans(trans, oldident, newident)
        for loc in temp.locations:
            loc.invariant.value = re.sub(regex, str(newident), loc.invariant.get_value())

    def inline_var_in_temp(self, temp, ident, val):
        """Returns a new template, with ident inlined to the given val."""
        regex = re.compile('(?<!\w)%s(?!\w)' % ident)
        toret = copy.deepcopy(temp)
        toret.declaration = re.sub(regex, str(val), toret.declaration)
        for trans in toret.transitions:
            self.inline_var_in_trans(trans, ident, val)
        #TODO: inline var in invariants
        return toret

    def inline_var_in_trans(self, trans, ident, val):
        """Inlines ident to the given val, in trans."""
        regex = re.compile('(?<!\w)%s(?!\w)' % ident)
        trans.select.value = re.sub(regex, str(val), trans.select.value)
        trans.guard.value = re.sub(regex, str(val), trans.guard.value)
        trans.assignment.value = re.sub(regex, str(val), trans.assignment.get_value())
        trans.synchronisation.value = re.sub(regex, str(val), trans.synchronisation.value)

if __name__ == '__main__':
    import sys
    file = open(sys.argv[1])
    nta = pyuppaal.NTA.from_xml(file)

    out_nta = SimplifyModel(nta).simplify()

    outfile = open(sys.argv[2], 'w')
    outfile.write(out_nta.to_xml())
