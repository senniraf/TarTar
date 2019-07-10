import traceback, sys

class Error(Exception):
    pass


def emergencyExit(str):
    traceback.print_exc(file=sys.stdout)
    print """

Error:
%s

If you need help to solve this error please feel free to contact us at: mchro@cs.aau.dk and andrease@cs.aau.dk. Please attach the model the error message.""" % str
    sys.exit(0)

def emergencyExitSytemDecl(str):
    emergencyExit(str+""" A parsing error occurred when parsing the system declaration/definition of the model. Please note that only a small subset of the UPPAAL system declaration language is supported. It is usually quite fast/trivial to rewrite the system declaration to the simplified subset supported by opaal. Unsupported features in the system declarations:
 * Variables
 * Priorities
 * Progress measures
 * and the old process notation""")
 
def emergencyExitUppaalCParser(str):
    emergencyExit(str+""" You probably have a syntax error or you are using some features that are still unsupported in your model. Please check that the model works in UPPAAL. An check that you are not using any of these unsupported features:
 * Passing arguments by reference
 * The conditional operator, i.e. (x==5) ? 1 : 0
 * Have methods in multiple templates with conflicting names
 * Use a type to declare an array size, i.e. int a[id_t]
""")

# vim:ts=4:sw=4:expandtab
