# -*- coding: utf-8 -*-
### BEGIN LICENSE
# Copyright (C) 2013 Mads Chr. Olesen <mchro@cs.aau.dk>
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

from base_lattice import BaseLattice

import logging
logger = logging.getLogger('capron')
#logger.setLevel(logging.DEBUG)

class ApronOctagon(BaseLattice):
    """
    Implementation of the Octagon lattice [1], using the APRON library [2].
    Generates C code.

    [1] The octagon abstract domain, Antoine Mine
    [2] http://apron.cri.ensmp.fr/library/
    """
    def __init__(self, dimensions=None, name=None, context=None):
        """
        Dimension should be number of variables in octagon.
        """
        dimensions = dimensions or (1, )
        assert len(dimensions) == 1, "Octagon only supports one dimension"
        self.dimensions = dimensions
        self.name = name
        self.context = context
        self.child_int_variables = []
        self.child_float_variables = []

    def addChildVariable(self, vtype, vident, vdimensions):
        assert len(vdimensions) == 0, "Octagon child variables must be singleton"
        assert len(vtype) == 1, "child child variables not supported"
        vtype = vtype[0]
        if vtype == "intvar":
            self.child_int_variables.append(vident)
        elif vtype == "floatvar":
            self.child_float_variables.append(vident)
        else:
            assert False, "Octagon child variables must be intvar or floatvar, not \"%s\"" % (vtype)

    def generateHeader(self):
        allvars = self.child_int_variables + self.child_float_variables
        var_ts = []
        oct_idents = []
        for x in allvars:
            self.context.constants.pop(x, None)
            var_ts.append("static void* %s = (void*)\"%s\";" % (x,x))
            oct_idents.append("(void*)%s" % (x))
        var_ts = "\n".join(var_ts)
        oct_idents = ", ".join(oct_idents)

        #XXX add support for child_float_variables
        assert len(self.child_float_variables) == 0, "floatvar's not fully supported yet"

        toret = """
#include <ap_global1.h>
#include <oct.h>

// APRON manager is per thread
__thread ap_manager_t* %(name)s_oct_man;

//XXX ugly
%(var_ts)s

static ap_var_t %(name)s_oct_idents[%(nvars)d] = {    
%(oct_idents)s
};


static ap_environment_t* %(name)s_oct_env = ap_environment_alloc(
    &%(name)s_oct_idents[0],%(nvars)d, /* integer variables */
    NULL,0                     /* real-valued variables */
    );

ap_abstract1_t* %(name)s_oct_clone(ap_abstract1_t* a) {
    ap_abstract1_t *toret = (ap_abstract1_t*)malloc(sizeof(ap_abstract1_t));
    *toret = ap_abstract1_copy(%(name)s_oct_man, a);
    return toret;
}

""" % {'name': self.name, 'var_ts': var_ts, 'oct_idents': oct_idents, 'nvars': len(allvars), 'nintvars': len(self.child_int_variables), 'nfloatvars': len(self.child_float_variables)}
        return toret

    @classmethod
    def getCompilerLinkFlags(cls):
        return "-lapron -lgmp -loctMPQ -lmpfr"

    def generateStateStructPart(self):
        return "ap_abstract1_t *%s;" % (self.name);

    def generateInitialStatePart(self):
        return "NULL, /* %s */" % (self.name)

    def generateInitialFuncPart(self, state_name):
        #XXX how to initialise _oct_man and _oct_env in threadsafe manner?
        return """
    //Initialise _oct_man in threadsafe manner
    %(name)s_oct_man = oct_manager_alloc();

    //%(name)s_oct_top = ap_abstract1_top(oct_oct_man, oct_oct_env);

    ap_abstract1_t top = ap_abstract1_top(%(name)s_oct_man, %(name)s_oct_env);
    %(state_name)s.%(name)s = %(name)s_oct_clone(&top);
    //%(state_name)s.%(name)s = &%(name)s_oct_top;
    //%(state_name)s.%(name)s = %(name)s_oct_clone(&%(name)s_oct_top);
""" % \
        {
            'state_name': state_name,
            'name': self.name,
            'd': self.dimensions[0]
        }

    def generateCopyPart(self, in_state_name, out_state_name):
        return """
        ap_abstract1_t out%(sname)s = 
            ap_abstract1_copy(%(sname)s_oct_man, (ap_abstract1_t*)%(in)s->%(sname)s);
        %(out)s->%(sname)s = &out%(sname)s;
""" % {
            'd': self.dimensions[0], 'out': out_state_name, 'sname': self.name, 'in': in_state_name
            }

    def generateLatticePrintPart(self, a):
        return """
    FILE *stream;
    char *buf;
    size_t len;

    stream = open_memstream (&buf, &len);
    if (stream == NULL)
        return "open_memstream failed";

    ap_abstract1_fprint(stream, %(name)s_oct_man, (ap_abstract1_t*)%(a)s);
    fflush (stream);
    /* remove special characters */
    for (int i = 0; i < len; i++) {
        if (buf[i] == 10)
            buf[i] = ';';
    }
    buf[len] = 0;

    return buf;
""" % \
        {
            'name': self.name,
            'a': a,
            'd': self.dimensions[0]
        }

    def generateLatticeClonePart(self, a):
        return "%(name)s_oct_clone((ap_abstract1_t*)%(a)s);" % {
                'name': self.name, 'a': a};

    def generateLatticeDeletePart(self, a):
        return "ap_abstract1_clear (%(name)s_oct_man, (ap_abstract1_t*)%(a)s);" % {
                'name': self.name, 'a': a};

    def generateLatticeCmpPart(self, a, b):
        return "ap_abstract1_is_eq(%(name)s_oct_man, (ap_abstract1_t*)%(a)s, (ap_abstract1_t*)%(b)s)" % {
                'name': self.name,
                'a': a,
                'b': b,
                }

    def generateLatticeHashPart(self, a):
        return "ap_abstract1_hash(%(name)s_oct_man, (ap_abstract1_t*)%(a)s)" % {
                'name': self.name,
                'a': a,
                }

    def generateCallbackPart(self, out):
        return "ap_abstract1_canonicalize(%(name)s_oct_man, (ap_abstract1_t*)%(out)s->%(name)s);" % {
                'name': self.name,
                'out': out,
                }

    def generateApplyInvariantPart(self, out):
        return "if (ap_abstract1_is_bottom(%(name)s_oct_man, (ap_abstract1_t*)%(out)s->%(name)s)) return false;" % {
                'name': self.name,
                'out': out,
                }



    def generateJoinPart(self, a, b):
        """ a = a join b"""
        return """
    ap_abstract1_t joined = ap_abstract1_copy(%(name)s_oct_man, *(ap_abstract1_t**)%(a)s);
    ap_abstract1_join(%(name)s_oct_man, true, &joined, *(ap_abstract1_t**)%(b)s);
    ap_abstract1_widening(%(name)s_oct_man, *(ap_abstract1_t**)%(a)s, &joined);
    ap_abstract1_clear(%(name)s_oct_man, &joined);
    return 1;""" % {
                'name': self.name,
                'a': a,
                'b': b,
                }

    def generateCoverPart(self, a, b):
        """a <= b"""
        return "ap_abstract1_is_leq(%(name)s_oct_man, *(ap_abstract1_t**)%(a)s, *(ap_abstract1_t**)%(b)s)" % {
                'name': self.name,
                'a': a,
                'b': b,
                }

    # Operations {{{
    #XXX think about how to hook these better into the c-code generation
    def generateExtraLatticeFunctions(self):
        return """
// x = [c1, c2]
void oct_updateValueInterval(state_struct_t *out, const ap_var_t var, int inf, int sup) {
    ap_linexpr1_t expr = ap_linexpr1_make(oct_oct_env,AP_LINEXPR_SPARSE,2);
    ap_linexpr1_set_cst_interval_int(&expr, inf, sup);

    ap_abstract1_assign_linexpr(oct_oct_man, true, (ap_abstract1_t*)out->oct, (ap_var_t)var, &expr, NULL);
    ap_linexpr1_clear(&expr);
}

//x = x + [c1, c2]
void oct_updateIncrementInterval(state_struct_t *out, const ap_var_t var, int inf, int sup) {
    ap_linexpr1_t expr = ap_linexpr1_make(oct_oct_env,AP_LINEXPR_SPARSE,4);

    ap_linexpr1_set_list(&expr,
            AP_CST_I_INT, inf, sup,
            AP_COEFF_S_INT, 1, var,
            AP_END);
    //ap_linexpr1_set_cst_interval_int(&expr, inf, sup);

    ap_abstract1_assign_linexpr(oct_oct_man, true, (ap_abstract1_t*)out->oct, (ap_var_t)var, &expr, NULL);
    ap_linexpr1_clear(&expr);
}

//x = y + [c1, c2]
void oct_updateVariableInterval(state_struct_t *out, const ap_var_t lvar, const ap_var_t rvar, int inf, int sup) {
    ap_linexpr1_t expr = ap_linexpr1_make(oct_oct_env,AP_LINEXPR_SPARSE,4);

    ap_linexpr1_set_list(&expr,
            AP_CST_I_INT, inf, sup,
            AP_COEFF_S_INT, 1, rvar,
            AP_END);
    //ap_linexpr1_set_cst_interval_int(&expr, inf, sup);

    ap_abstract1_assign_linexpr(oct_oct_man, true, (ap_abstract1_t*)out->oct, (ap_var_t)lvar, &expr, NULL);
    ap_linexpr1_clear(&expr);
}


//x = x + y
void oct_updateIncrementVariable(state_struct_t *out, const ap_var_t lvar, const ap_var_t rvar) {
    ap_linexpr1_t expr = ap_linexpr1_make(oct_oct_env,AP_LINEXPR_SPARSE,4);

    ap_linexpr1_set_list(&expr,
            AP_COEFF_S_INT, 1, lvar,
            AP_COEFF_S_INT, 1, rvar,
            AP_END);
    //ap_linexpr1_set_cst_interval_int(&expr, inf, sup);

    ap_abstract1_assign_linexpr(oct_oct_man, true, (ap_abstract1_t*)out->oct, (ap_var_t)lvar, &expr, NULL);
    ap_linexpr1_clear(&expr);
}


void oct_assumeInterval(state_struct_t *out, const ap_var_t var, int inf, int sup) {
    ap_lincons1_array_t array = ap_lincons1_array_make(oct_oct_env,1);

    ap_linexpr1_t expr = ap_linexpr1_make(oct_oct_env,AP_LINEXPR_SPARSE,2);

    ap_linexpr1_set_list(&expr,
            AP_COEFF_S_INT, -1, var,
            AP_CST_I_INT, inf, sup,
            AP_END);

    ap_lincons1_t cons = ap_lincons1_make(AP_CONS_EQ,&expr,NULL);
    ap_lincons1_array_set(&array,0,&cons);    
    
    ap_abstract1_meet_lincons_array(oct_oct_man, true, (ap_abstract1_t*)out->oct, &array);
    ap_lincons1_array_clear(&array);
}
"""
    #}}}


