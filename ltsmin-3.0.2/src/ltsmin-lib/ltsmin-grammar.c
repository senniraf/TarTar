/* Driver template for the LEMON parser generator.
** The author disclaims copyright to this source code.
*/
/* First off, code is included that follows the "include" declaration
** in the input grammar file. */
#include <stdio.h>
#line 1 "ltsmin-grammar.lemon"

#include <hre/config.h>
#include <stdlib.h>

#include <hre/user.h>
#include <util-lib/chunk_support.h>
#include <ltsmin-lib/etf-util.h>
#include <ltsmin-lib/etf-internal.h>
#include <ltsmin-lib/ltsmin-parse-env.h>
#include <ltsmin-lib/ltsmin-standard.h>
/* solves the issue where lemon parses this file
 with -Werror and -DNDEBUG */
#ifdef NDEBUG
#undef NDEBUG
#endif
#include <assert.h>
#line 25 "ltsmin-grammar.c"
/* Next is all token values, in a form suitable for use by makeheaders.
** This section will be null unless lemon is run with the -m switch.
*/
/* 
** These constants (all generated automatically by the parser generator)
** specify the various kinds of tokens (terminals) that the parser
** understands. 
**
** Each symbol here is a terminal symbol in the grammar.
*/
/* Make sure the INTERFACE macro is defined.
*/
#ifndef INTERFACE
# define INTERFACE 1
#endif
/* The next thing included is series of defines which control
** various aspects of the generated parser.
**    YYCODETYPE         is the data type used for storing terminal
**                       and nonterminal numbers.  "unsigned char" is
**                       used if there are fewer than 250 terminals
**                       and nonterminals.  "int" is used otherwise.
**    YYNOCODE           is a number of type YYCODETYPE which corresponds
**                       to no legal terminal or nonterminal number.  This
**                       number is used to fill in empty slots of the hash 
**                       table.
**    YYFALLBACK         If defined, this indicates that one or more tokens
**                       have fall-back values which should be used if the
**                       original value of the token will not parse.
**    YYACTIONTYPE       is the data type used for storing terminal
**                       and nonterminal numbers.  "unsigned char" is
**                       used if there are fewer than 250 rules and
**                       states combined.  "int" is used otherwise.
**    ParseTOKENTYPE     is the data type used for minor tokens given 
**                       directly to the parser from the tokenizer.
**    YYMINORTYPE        is the data type used for all minor tokens.
**                       This is typically a union of many types, one of
**                       which is ParseTOKENTYPE.  The entry in the union
**                       for base tokens is called "yy0".
**    YYSTACKDEPTH       is the maximum depth of the parser's stack.  If
**                       zero the stack is dynamically sized using realloc()
**    ParseARG_SDECL     A static variable declaration for the %extra_argument
**    ParseARG_PDECL     A parameter declaration for the %extra_argument
**    ParseARG_STORE     Code to store %extra_argument into yypParser
**    ParseARG_FETCH     Code to extract %extra_argument from yypParser
**    YYNSTATE           the combined number of states.
**    YYNRULE            the number of rules in the grammar
**    YYERRORSYMBOL      is the code number of the error symbol.  If not
**                       defined, then do no error processing.
*/
#define YYCODETYPE unsigned char
#define YYNOCODE 87
#define YYACTIONTYPE unsigned char
#define ParseTOKENTYPE  int 
typedef union {
  int yyinit;
  ParseTOKENTYPE yy0;
  int yy64;
  etf_map_t yy88;
  ltsmin_expr_t yy125;
  etf_list_t yy130;
  string_index_t yy138;
  etf_rel_t yy153;
  int yy173;
} YYMINORTYPE;
#ifndef YYSTACKDEPTH
#define YYSTACKDEPTH 100
#endif
#define ParseARG_SDECL  ltsmin_parse_env_t env ;
#define ParseARG_PDECL , ltsmin_parse_env_t env 
#define ParseARG_FETCH  ltsmin_parse_env_t env  = yypParser->env 
#define ParseARG_STORE yypParser->env  = env 
#define YYNSTATE 151
#define YYNRULE 81
#define YYERRORSYMBOL 67
#define YYERRSYMDT yy173
#define YY_NO_ACTION      (YYNSTATE+YYNRULE+2)
#define YY_ACCEPT_ACTION  (YYNSTATE+YYNRULE+1)
#define YY_ERROR_ACTION   (YYNSTATE+YYNRULE)

/* The yyzerominor constant is used to initialize instances of
** YYMINORTYPE objects to zero. */
static const YYMINORTYPE yyzerominor = { 0 };


/* Next are the tables used to determine what action to take based on the
** current state and lookahead token.  These tables are used to implement
** functions that take a state number and lookahead value and return an
** action integer.  
**
** Suppose the action integer is N.  Then the action is determined as
** follows
**
**   0 <= N < YYNSTATE                  Shift N.  That is, push the lookahead
**                                      token onto the stack and goto state N.
**
**   YYNSTATE <= N < YYNSTATE+YYNRULE   Reduce by rule N-YYNSTATE.
**
**   N == YYNSTATE+YYNRULE              A syntax error has occurred.
**
**   N == YYNSTATE+YYNRULE+1            The parser accepts its input.
**
**   N == YYNSTATE+YYNRULE+2            No such action.  Denotes unused
**                                      slots in the yy_action[] table.
**
** The action table is constructed as a single large table named yy_action[].
** Given state S and lookahead X, the action is computed as
**
**      yy_action[ yy_shift_ofst[S] + X ]
**
** If the index value yy_shift_ofst[S]+X is out of range or if the value
** yy_lookahead[yy_shift_ofst[S]+X] is not equal to X or if yy_shift_ofst[S]
** is equal to YY_SHIFT_USE_DFLT, it means that the action is not in the table
** and that yy_default[S] should be used instead.  
**
** The formula above is for computing the action when the lookahead is
** a terminal symbol.  If the lookahead is a non-terminal (as occurs after
** a reduce action) then the yy_reduce_ofst[] array is used in place of
** the yy_shift_ofst[] array and YY_REDUCE_USE_DFLT is used in place of
** YY_SHIFT_USE_DFLT.
**
** The following are the tables generated in this section:
**
**  yy_action[]        A single table containing all actions.
**  yy_lookahead[]     A table containing the lookahead for each entry in
**                     yy_action.  Used to detect hash collisions.
**  yy_shift_ofst[]    For each state, the offset into yy_action for
**                     shifting terminals.
**  yy_reduce_ofst[]   For each state, the offset into yy_action for
**                     shifting non-terminals after a reduce.
**  yy_default[]       Default action for each state.
*/
static const YYACTIONTYPE yy_action[] = {
 /*     0 */   140,  233,  137,  144,    8,  139,  143,    6,  133,  142,
 /*    10 */     1,   39,  141,   93,  119,  148,   12,   26,  147,   11,
 /*    20 */    25,  146,   10,   24,  145,    9,   23,  144,    8,   22,
 /*    30 */   143,    6,   21,  142,  151,   20,  188,   71,   19,   86,
 /*    40 */    44,   18,  119,    7,  128,  136,  138,   97,  127,   99,
 /*    50 */    29,   31,  101,  125,  103,   84,  105,   36,   17,   16,
 /*    60 */    15,  107,  150,   14,   45,  149,   13,   74,  148,   12,
 /*    70 */    69,  147,   11,   67,  146,   10,   65,  145,    9,   63,
 /*    80 */   144,    8,   61,  143,    6,   59,  142,   81,   17,   16,
 /*    90 */    15,   72,  150,   14,   85,  149,   13,   57,  148,   12,
 /*   100 */    56,  147,   11,   55,  146,   10,   96,  145,    9,   75,
 /*   110 */   144,    8,   70,  143,    6,   68,  142,   80,  135,   17,
 /*   120 */    16,   15,   76,  150,   14,  116,  149,   13,   66,  148,
 /*   130 */    12,   64,  147,   11,   62,  146,   10,   60,  145,    9,
 /*   140 */    58,  144,    8,   48,  143,    6,   49,  142,   46,   50,
 /*   150 */    17,   16,   15,   30,  150,   14,   47,  149,   13,   51,
 /*   160 */   148,   12,   52,  147,   11,   53,  146,   10,   54,  145,
 /*   170 */     9,  117,  144,    8,   87,  143,    6,    3,  142,   89,
 /*   180 */   130,   17,   16,   15,   32,  150,   14,   73,  149,   13,
 /*   190 */     4,  148,   12,   77,  147,   11,   78,  146,   10,  112,
 /*   200 */   145,    9,  115,  144,    8,  118,  143,    6,  122,  142,
 /*   210 */    16,   15,   83,  150,   14,  126,  149,   13,  124,  148,
 /*   220 */    12,  179,  147,   11,   88,  146,   10,  129,  145,    9,
 /*   230 */    42,  144,    8,  131,  143,    6,   15,  142,  150,   14,
 /*   240 */    92,  149,   13,  132,  148,   12,   43,  147,   11,  134,
 /*   250 */   146,   10,  152,  145,    9,  104,  144,    8,  142,  143,
 /*   260 */     6,   98,  142,  150,   14,   27,  149,   13,  100,  148,
 /*   270 */    12,   28,  147,   11,  102,  146,   10,   33,  145,    9,
 /*   280 */   106,  144,    8,   34,  143,    6,   35,  142,  234,  149,
 /*   290 */    13,  234,  148,   12,  234,  147,   11,  234,  146,   10,
 /*   300 */   234,  145,    9,  234,  144,    8,  234,  143,    6,  234,
 /*   310 */   142,  147,   11,  234,  146,   10,  234,  145,    9,  234,
 /*   320 */   144,    8,  234,  143,    6,  234,  142,  234,  146,   10,
 /*   330 */   234,  145,    9,  234,  144,    8,  234,  143,    6,  234,
 /*   340 */   142,  145,    9,  234,  144,    8,  234,  143,    6,  234,
 /*   350 */   142,  108,  109,  110,  111,   40,    2,   95,  234,   82,
 /*   360 */    37,  234,   41,   38,  123,  234,   79,  120,  121,  113,
 /*   370 */   114,  234,  143,    6,    5,  142,   90,  234,   94,  234,
 /*   380 */   234,   91,  234,   91,
};
static const YYCODETYPE yy_lookahead[] = {
 /*     0 */     8,   68,   10,   44,   45,   13,   47,   48,   67,   50,
 /*    10 */    69,   70,   20,    3,    5,   32,   33,   25,   35,   36,
 /*    20 */    28,   38,   39,   31,   41,   42,   34,   44,   45,   37,
 /*    30 */    47,   48,   40,   50,    0,   43,    0,    3,   46,    8,
 /*    40 */    85,   49,    5,   51,   13,   53,   54,   55,   17,   57,
 /*    50 */    58,   59,   60,   16,   62,   80,   64,   82,   22,   23,
 /*    60 */    24,   85,   26,   27,   85,   29,   30,   85,   32,   33,
 /*    70 */    85,   35,   36,   85,   38,   39,   85,   41,   42,   85,
 /*    80 */    44,   45,   85,   47,   48,   85,   50,   80,   22,   23,
 /*    90 */    24,   84,   26,   27,   83,   29,   30,   85,   32,   33,
 /*   100 */    85,   35,   36,   85,   38,   39,   85,   41,   42,   85,
 /*   110 */    44,   45,   85,   47,   48,   85,   50,    5,   52,   22,
 /*   120 */    23,   24,   78,   26,   27,   13,   29,   30,   85,   32,
 /*   130 */    33,   85,   35,   36,   85,   38,   39,   85,   41,   42,
 /*   140 */    85,   44,   45,   85,   47,   48,   85,   50,   85,   85,
 /*   150 */    22,   23,   24,   56,   26,   27,   85,   29,   30,   85,
 /*   160 */    32,   33,   85,   35,   36,   85,   38,   39,   85,   41,
 /*   170 */    42,   10,   44,   45,   10,   47,   48,   81,   50,    3,
 /*   180 */    71,   22,   23,   24,   56,   26,   27,   77,   29,   30,
 /*   190 */    79,   32,   33,   76,   35,   36,   76,   38,   39,    7,
 /*   200 */    41,   42,   12,   44,   45,   14,   47,   48,    8,   50,
 /*   210 */    23,   24,   18,   26,   27,   16,   29,   30,   15,   32,
 /*   220 */    33,   16,   35,   36,   11,   38,   39,   10,   41,   42,
 /*   230 */     6,   44,   45,    6,   47,   48,   24,   50,   26,   27,
 /*   240 */    11,   29,   30,   10,   32,   33,    4,   35,   36,    4,
 /*   250 */    38,   39,    0,   41,   42,   54,   44,   45,   50,   47,
 /*   260 */    48,   10,   50,   26,   27,   56,   29,   30,   10,   32,
 /*   270 */    33,   56,   35,   36,   10,   38,   39,   61,   41,   42,
 /*   280 */    54,   44,   45,   63,   47,   48,   65,   50,   86,   29,
 /*   290 */    30,   86,   32,   33,   86,   35,   36,   86,   38,   39,
 /*   300 */    86,   41,   42,   86,   44,   45,   86,   47,   48,   86,
 /*   310 */    50,   35,   36,   86,   38,   39,   86,   41,   42,   86,
 /*   320 */    44,   45,   86,   47,   48,   86,   50,   86,   38,   39,
 /*   330 */    86,   41,   42,   86,   44,   45,   86,   47,   48,   86,
 /*   340 */    50,   41,   42,   86,   44,   45,   86,   47,   48,   86,
 /*   350 */    50,   72,   73,   74,   75,    7,    1,    2,   86,    8,
 /*   360 */    12,   86,   14,   15,   13,   86,    5,   16,   17,    8,
 /*   370 */     9,   86,   47,   48,   19,   50,    5,   86,    5,   86,
 /*   380 */    86,   10,   86,   10,
};
#define YY_SHIFT_USE_DFLT (-42)
#define YY_SHIFT_MAX 107
static const short yy_shift_ofst[] = {
 /*     0 */   355,   34,   10,   37,    9,   -8,   -8,   -8,   -8,   -8,
 /*    10 */    -8,   -8,   -8,   -8,   -8,   -8,   -8,   -8,   -8,   -8,
 /*    20 */    -8,   -8,   -8,   -8,   -8,   -8,   -8,   -8,   -8,   -8,
 /*    30 */    -8,   -8,   -8,   -8,   -8,   -8,   31,  161,  164,  176,
 /*    40 */   -42,  -42,  -42,  -42,   36,   66,   97,  128,  159,  159,
 /*    50 */   159,  159,  159,  159,  159,  187,  212,  237,  237,  260,
 /*    60 */   260,  -17,  -17,  276,  276,  290,  290,  300,  300,  -41,
 /*    70 */   -41,  348,  351,  361,  325,  325,  112,  371,  373,  192,
 /*    80 */   190,  191,  194,  200,  203,  199,  205,  213,  217,  224,
 /*    90 */   227,  229,  233,  242,  245,  252,  208,  251,  209,  258,
 /*   100 */   215,  264,  216,  201,  220,  226,  221,  208,
};
#define YY_REDUCE_USE_DFLT (-68)
#define YY_REDUCE_MAX 43
static const short yy_reduce_ofst[] = {
 /*     0 */   -67,  279,  -59,  -25,    7,  -45,  -24,  -21,  -18,  -15,
 /*    10 */   -12,   -9,   -6,   -3,    0,   12,   15,   18,   21,   24,
 /*    20 */    27,   30,   43,   46,   49,   52,   55,   58,   61,   63,
 /*    30 */    64,   71,   74,   77,   80,   83,   11,   44,   96,  109,
 /*    40 */   110,  111,  117,  120,
};
static const YYACTIONTYPE yy_default[] = {
 /*     0 */   232,  232,  232,  176,  183,  232,  232,  232,  232,  232,
 /*    10 */   232,  232,  232,  232,  232,  232,  232,  232,  232,  232,
 /*    20 */   232,  232,  232,  232,  232,  232,  232,  232,  232,  232,
 /*    30 */   232,  232,  232,  232,  232,  232,  232,  232,  232,  232,
 /*    40 */   162,  181,  165,  165,  232,  232,  232,  232,  225,  226,
 /*    50 */   227,  228,  229,  230,  231,  206,  205,  204,  215,  203,
 /*    60 */   214,  202,  213,  201,  212,  200,  211,  199,  210,  198,
 /*    70 */   209,  232,  232,  232,  197,  208,  232,  232,  232,  232,
 /*    80 */   232,  232,  186,  232,  232,  232,  177,  232,  232,  232,
 /*    90 */   232,  232,  232,  232,  232,  232,  207,  232,  232,  232,
 /*   100 */   232,  232,  232,  232,  232,  232,  232,  196,  154,  155,
 /*   110 */   156,  157,  161,  163,  164,  167,  169,  168,  170,  171,
 /*   120 */   182,  184,  185,  187,  172,  174,  175,  178,  180,  173,
 /*   130 */   153,  160,  166,  158,  159,  189,  190,  191,  192,  193,
 /*   140 */   194,  195,  216,  217,  218,  219,  220,  221,  222,  223,
 /*   150 */   224,
};
#define YY_SZ_ACTTAB (int)(sizeof(yy_action)/sizeof(yy_action[0]))

/* The next table maps tokens into fallback tokens.  If a construct
** like the following:
** 
**      %fallback ID X Y Z.
**
** appears in the grammar, then ID becomes a fallback token for X, Y,
** and Z.  Whenever one of the tokens X, Y, or Z is input to the parser
** but it does not parse, the type of the token is changed to ID and
** the parse is retried before an error is thrown.
*/
#ifdef YYFALLBACK
static const YYCODETYPE yyFallback[] = {
};
#endif /* YYFALLBACK */

/* The following structure represents a single element of the
** parser's stack.  Information stored includes:
**
**   +  The state number for the parser at this level of the stack.
**
**   +  The value of the token stored at this level of the stack.
**      (In other words, the "major" token.)
**
**   +  The semantic value stored at this level of the stack.  This is
**      the information used by the action routines in the grammar.
**      It is sometimes called the "minor" token.
*/
struct yyStackEntry {
  YYACTIONTYPE stateno;  /* The state-number */
  YYCODETYPE major;      /* The major token value.  This is the code
                         ** number for the token at this stack level */
  YYMINORTYPE minor;     /* The user-supplied minor token value.  This
                         ** is the value of the token  */
};
typedef struct yyStackEntry yyStackEntry;

/* The state of the parser is completely contained in an instance of
** the following structure */
struct yyParser {
  int yyidx;                    /* Index of top element in stack */
#ifdef YYTRACKMAXSTACKDEPTH
  int yyidxMax;                 /* Maximum value of yyidx */
#endif
  int yyerrcnt;                 /* Shifts left before out of the error */
  ParseARG_SDECL                /* A place to hold %extra_argument */
#if YYSTACKDEPTH<=0
  int yystksz;                  /* Current side of the stack */
  yyStackEntry *yystack;        /* The parser's stack */
#else
  yyStackEntry yystack[YYSTACKDEPTH];  /* The parser's stack */
#endif
};
typedef struct yyParser yyParser;

#ifndef NDEBUG
#include <stdio.h>
static FILE *yyTraceFILE = 0;
static char *yyTracePrompt = 0;
#endif /* NDEBUG */

#ifndef NDEBUG
/* 
** Turn parser tracing on by giving a stream to which to write the trace
** and a prompt to preface each trace message.  Tracing is turned off
** by making either argument NULL 
**
** Inputs:
** <ul>
** <li> A FILE* to which trace output should be written.
**      If NULL, then tracing is turned off.
** <li> A prefix string written at the beginning of every
**      line of trace output.  If NULL, then tracing is
**      turned off.
** </ul>
**
** Outputs:
** None.
*/
void ParseTrace(FILE *TraceFILE, char *zTracePrompt){
  yyTraceFILE = TraceFILE;
  yyTracePrompt = zTracePrompt;
  if( yyTraceFILE==0 ) yyTracePrompt = 0;
  else if( yyTracePrompt==0 ) yyTraceFILE = 0;
}
#endif /* NDEBUG */

#ifndef NDEBUG
/* For tracing shifts, the names of all terminals and nonterminals
** are required.  The following table supplies these names */
static const char *const yyTokenName[] = { 
  "$",             "ETF",           "ERROR",         "BEGIN",       
  "STATE",         "END",           "EDGE",          "INIT",        
  "NUMBER",        "STRING",        "IDENT",         "COLON",       
  "SORT",          "VALUE",         "TRANS",         "MAP",         
  "END_OF_LINE",   "STAR",          "SLASH",         "EXPR",        
  "CONSTANT",      "QUANTIFIER",    "BIN11",         "BIN10",       
  "BIN9",          "PREFIX9",       "POSTFIX9",      "BIN8",        
  "PREFIX8",       "POSTFIX8",      "BIN7",          "PREFIX7",     
  "POSTFIX7",      "BIN6",          "PREFIX6",       "POSTFIX6",    
  "BIN5",          "PREFIX5",       "POSTFIX5",      "BIN4",        
  "PREFIX4",       "POSTFIX4",      "BIN3",          "PREFIX3",     
  "POSTFIX3",      "BIN2",          "PREFIX2",       "POSTFIX2",    
  "BIN1",          "PREFIX1",       "POSTFIX1",      "LPAR",        
  "RPAR",          "STATE_VAR",     "EDGE_VAR",      "MU_SYM",      
  "DOT",           "NU_SYM",        "EXISTS_SYM",    "ALL_SYM",     
  "IF",            "THEN",          "EDGE_EXIST_LEFT",  "EDGE_EXIST_RIGHT",
  "EDGE_ALL_LEFT",  "EDGE_ALL_RIGHT",  "USER",          "error",       
  "input",         "etf_spec",      "state_section",  "edge_section",
  "init_section",  "trans_section",  "map_section",   "sort_section",
  "decl_list",     "valref_list",   "sort_list",     "trans_list",  
  "end",           "map_list",      "map_entry",     "value",       
  "step_list",     "expr",        
};
#endif /* NDEBUG */

#ifndef NDEBUG
/* For tracing reduce actions, the names of all rules are required.
*/
static const char *const yyRuleName[] = {
 /*   0 */ "input ::= ETF etf_spec",
 /*   1 */ "input ::= ERROR",
 /*   2 */ "etf_spec ::= state_section edge_section",
 /*   3 */ "etf_spec ::= etf_spec init_section",
 /*   4 */ "etf_spec ::= etf_spec trans_section",
 /*   5 */ "etf_spec ::= etf_spec map_section",
 /*   6 */ "etf_spec ::= etf_spec sort_section",
 /*   7 */ "etf_spec ::= error",
 /*   8 */ "state_section ::= BEGIN STATE decl_list END STATE",
 /*   9 */ "edge_section ::= BEGIN EDGE decl_list END EDGE",
 /*  10 */ "init_section ::= BEGIN INIT valref_list END INIT",
 /*  11 */ "valref_list ::=",
 /*  12 */ "valref_list ::= valref_list NUMBER",
 /*  13 */ "valref_list ::= valref_list STRING",
 /*  14 */ "decl_list ::=",
 /*  15 */ "decl_list ::= decl_list IDENT COLON IDENT",
 /*  16 */ "sort_section ::= BEGIN SORT sort_list END SORT",
 /*  17 */ "sort_list ::= IDENT",
 /*  18 */ "sort_list ::= sort_list VALUE",
 /*  19 */ "trans_section ::= BEGIN TRANS trans_list end TRANS",
 /*  20 */ "end ::= END",
 /*  21 */ "map_section ::= BEGIN MAP map_list end MAP",
 /*  22 */ "map_list ::= IDENT COLON IDENT",
 /*  23 */ "map_list ::= map_list END_OF_LINE",
 /*  24 */ "map_list ::= map_list map_entry value END_OF_LINE",
 /*  25 */ "map_entry ::=",
 /*  26 */ "map_entry ::= map_entry NUMBER",
 /*  27 */ "map_entry ::= map_entry STAR",
 /*  28 */ "value ::= NUMBER",
 /*  29 */ "value ::= VALUE",
 /*  30 */ "trans_list ::=",
 /*  31 */ "trans_list ::= trans_list step_list END_OF_LINE",
 /*  32 */ "step_list ::=",
 /*  33 */ "step_list ::= step_list STAR",
 /*  34 */ "step_list ::= step_list NUMBER SLASH NUMBER",
 /*  35 */ "step_list ::= step_list NUMBER",
 /*  36 */ "step_list ::= step_list VALUE",
 /*  37 */ "input ::= EXPR expr",
 /*  38 */ "expr ::= LPAR expr RPAR",
 /*  39 */ "expr ::= STATE_VAR",
 /*  40 */ "expr ::= IDENT",
 /*  41 */ "expr ::= EDGE_VAR",
 /*  42 */ "expr ::= VALUE",
 /*  43 */ "expr ::= NUMBER",
 /*  44 */ "expr ::= CONSTANT",
 /*  45 */ "expr ::= expr BIN1 expr",
 /*  46 */ "expr ::= expr BIN2 expr",
 /*  47 */ "expr ::= expr BIN3 expr",
 /*  48 */ "expr ::= expr BIN4 expr",
 /*  49 */ "expr ::= expr BIN5 expr",
 /*  50 */ "expr ::= expr BIN6 expr",
 /*  51 */ "expr ::= expr BIN7 expr",
 /*  52 */ "expr ::= expr BIN8 expr",
 /*  53 */ "expr ::= expr BIN9 expr",
 /*  54 */ "expr ::= expr BIN10 expr",
 /*  55 */ "expr ::= expr BIN11 expr",
 /*  56 */ "expr ::= PREFIX1 expr",
 /*  57 */ "expr ::= PREFIX2 expr",
 /*  58 */ "expr ::= PREFIX3 expr",
 /*  59 */ "expr ::= PREFIX4 expr",
 /*  60 */ "expr ::= PREFIX5 expr",
 /*  61 */ "expr ::= PREFIX6 expr",
 /*  62 */ "expr ::= PREFIX7 expr",
 /*  63 */ "expr ::= PREFIX8 expr",
 /*  64 */ "expr ::= PREFIX9 expr",
 /*  65 */ "expr ::= expr POSTFIX1",
 /*  66 */ "expr ::= expr POSTFIX2",
 /*  67 */ "expr ::= expr POSTFIX3",
 /*  68 */ "expr ::= expr POSTFIX4",
 /*  69 */ "expr ::= expr POSTFIX5",
 /*  70 */ "expr ::= expr POSTFIX6",
 /*  71 */ "expr ::= expr POSTFIX7",
 /*  72 */ "expr ::= expr POSTFIX8",
 /*  73 */ "expr ::= expr POSTFIX9",
 /*  74 */ "expr ::= MU_SYM IDENT DOT expr",
 /*  75 */ "expr ::= NU_SYM IDENT DOT expr",
 /*  76 */ "expr ::= EXISTS_SYM expr DOT expr",
 /*  77 */ "expr ::= ALL_SYM expr DOT expr",
 /*  78 */ "expr ::= IF IDENT THEN expr",
 /*  79 */ "expr ::= EDGE_EXIST_LEFT EDGE_VAR EDGE_EXIST_RIGHT expr",
 /*  80 */ "expr ::= EDGE_ALL_LEFT EDGE_VAR EDGE_ALL_RIGHT expr",
};
#endif /* NDEBUG */


#if YYSTACKDEPTH<=0
/*
** Try to increase the size of the parser stack.
*/
static void yyGrowStack(yyParser *p){
  int newSize;
  yyStackEntry *pNew;

  newSize = p->yystksz*2 + 100;
  pNew = realloc(p->yystack, newSize*sizeof(pNew[0]));
  if( pNew ){
    p->yystack = pNew;
    p->yystksz = newSize;
#ifndef NDEBUG
    if( yyTraceFILE ){
      fprintf(yyTraceFILE,"%sStack grows to %d entries!\n",
              yyTracePrompt, p->yystksz);
    }
#endif
  }
}
#endif

/* 
** This function allocates a new parser.
** The only argument is a pointer to a function which works like
** malloc.
**
** Inputs:
** A pointer to the function used to allocate memory.
**
** Outputs:
** A pointer to a parser.  This pointer is used in subsequent calls
** to Parse and ParseFree.
*/
void *ParseAlloc(void *(*mallocProc)(size_t)){
  yyParser *pParser;
  pParser = (yyParser*)(*mallocProc)( (size_t)sizeof(yyParser) );
  if( pParser ){
    pParser->yyidx = -1;
#ifdef YYTRACKMAXSTACKDEPTH
    pParser->yyidxMax = 0;
#endif
#if YYSTACKDEPTH<=0
    pParser->yystack = NULL;
    pParser->yystksz = 0;
    yyGrowStack(pParser);
#endif
  }
  return pParser;
}

/* The following function deletes the value associated with a
** symbol.  The symbol can be either a terminal or nonterminal.
** "yymajor" is the symbol code, and "yypminor" is a pointer to
** the value.
*/
static void yy_destructor(
  yyParser *yypParser,    /* The parser */
  YYCODETYPE yymajor,     /* Type code for object to destroy */
  YYMINORTYPE *yypminor   /* The object to be destroyed */
){
  ParseARG_FETCH;
  switch( yymajor ){
    /* Here is inserted the actions which take place when a
    ** terminal or non-terminal is destroyed.  This can happen
    ** when the symbol is popped from the stack during a
    ** reduce or during error processing or when a parser is 
    ** being destroyed before it is finished parsing.
    **
    ** Note: during a reduce, the only symbols destroyed are those
    ** which appear on the RHS of the rule, but which are not used
    ** inside the C code.
    */
    case 76: /* decl_list */
    case 77: /* valref_list */
    case 82: /* map_entry */
    case 84: /* step_list */
{
#line 156 "ltsmin-grammar.lemon"
 ETFlistFree((yypminor->yy130)); 
#line 568 "ltsmin-grammar.c"
}
      break;
    case 85: /* expr */
{
#line 321 "ltsmin-grammar.lemon"

    (void)env;
     LTSminExprDestroy((yypminor->yy125), 1);

#line 578 "ltsmin-grammar.c"
}
      break;
    default:  break;   /* If no destructor action specified: do nothing */
  }
}

/*
** Pop the parser's stack once.
**
** If there is a destructor routine associated with the token which
** is popped from the stack, then call it.
**
** Return the major token number for the symbol popped.
*/
static int yy_pop_parser_stack(yyParser *pParser){
  YYCODETYPE yymajor;
  yyStackEntry *yytos = &pParser->yystack[pParser->yyidx];

  if( pParser->yyidx<0 ) return 0;
#ifndef NDEBUG
  if( yyTraceFILE && pParser->yyidx>=0 ){
    fprintf(yyTraceFILE,"%sPopping %s\n",
      yyTracePrompt,
      yyTokenName[yytos->major]);
  }
#endif
  yymajor = yytos->major;
  yy_destructor(pParser, yymajor, &yytos->minor);
  pParser->yyidx--;
  return yymajor;
}

/* 
** Deallocate and destroy a parser.  Destructors are all called for
** all stack elements before shutting the parser down.
**
** Inputs:
** <ul>
** <li>  A pointer to the parser.  This should be a pointer
**       obtained from ParseAlloc.
** <li>  A pointer to a function used to reclaim memory obtained
**       from malloc.
** </ul>
*/
void ParseFree(
  void *p,                    /* The parser to be deleted */
  void (*freeProc)(void*)     /* Function used to reclaim memory */
){
  yyParser *pParser = (yyParser*)p;
  if( pParser==0 ) return;
  while( pParser->yyidx>=0 ) yy_pop_parser_stack(pParser);
#if YYSTACKDEPTH<=0
  free(pParser->yystack);
#endif
  (*freeProc)((void*)pParser);
}

/*
** Return the peak depth of the stack for a parser.
*/
#ifdef YYTRACKMAXSTACKDEPTH
int ParseStackPeak(void *p){
  yyParser *pParser = (yyParser*)p;
  return pParser->yyidxMax;
}
#endif

/*
** Find the appropriate action for a parser given the terminal
** look-ahead token iLookAhead.
**
** If the look-ahead token is YYNOCODE, then check to see if the action is
** independent of the look-ahead.  If it is, return the action, otherwise
** return YY_NO_ACTION.
*/
static int yy_find_shift_action(
  yyParser *pParser,        /* The parser */
  YYCODETYPE iLookAhead     /* The look-ahead token */
){
  int i;
  int stateno = pParser->yystack[pParser->yyidx].stateno;
 
  if( stateno>YY_SHIFT_MAX || (i = yy_shift_ofst[stateno])==YY_SHIFT_USE_DFLT ){
    return yy_default[stateno];
  }
  assert( iLookAhead!=YYNOCODE );
  i += iLookAhead;
  if( i<0 || i>=YY_SZ_ACTTAB || yy_lookahead[i]!=iLookAhead ){
    if( iLookAhead>0 ){
#ifdef YYFALLBACK
      YYCODETYPE iFallback;            /* Fallback token */
      if( iLookAhead<sizeof(yyFallback)/sizeof(yyFallback[0])
             && (iFallback = yyFallback[iLookAhead])!=0 ){
#ifndef NDEBUG
        if( yyTraceFILE ){
          fprintf(yyTraceFILE, "%sFALLBACK %s => %s\n",
             yyTracePrompt, yyTokenName[iLookAhead], yyTokenName[iFallback]);
        }
#endif
        return yy_find_shift_action(pParser, iFallback);
      }
#endif
#ifdef YYWILDCARD
      {
        int j = i - iLookAhead + YYWILDCARD;
        if( j>=0 && j<YY_SZ_ACTTAB && yy_lookahead[j]==YYWILDCARD ){
#ifndef NDEBUG
          if( yyTraceFILE ){
            fprintf(yyTraceFILE, "%sWILDCARD %s => %s\n",
               yyTracePrompt, yyTokenName[iLookAhead], yyTokenName[YYWILDCARD]);
          }
#endif /* NDEBUG */
          return yy_action[j];
        }
      }
#endif /* YYWILDCARD */
    }
    return yy_default[stateno];
  }else{
    return yy_action[i];
  }
}

/*
** Find the appropriate action for a parser given the non-terminal
** look-ahead token iLookAhead.
**
** If the look-ahead token is YYNOCODE, then check to see if the action is
** independent of the look-ahead.  If it is, return the action, otherwise
** return YY_NO_ACTION.
*/
static int yy_find_reduce_action(
  int stateno,              /* Current state number */
  YYCODETYPE iLookAhead     /* The look-ahead token */
){
  int i;
#ifdef YYERRORSYMBOL
  if( stateno>YY_REDUCE_MAX ){
    return yy_default[stateno];
  }
#else
  assert( stateno<=YY_REDUCE_MAX );
#endif
  i = yy_reduce_ofst[stateno];
  assert( i!=YY_REDUCE_USE_DFLT );
  assert( iLookAhead!=YYNOCODE );
  i += iLookAhead;
#ifdef YYERRORSYMBOL
  if( i<0 || i>=YY_SZ_ACTTAB || yy_lookahead[i]!=iLookAhead ){
    return yy_default[stateno];
  }
#else
  assert( i>=0 && i<YY_SZ_ACTTAB );
  assert( yy_lookahead[i]==iLookAhead );
#endif
  return yy_action[i];
}

/*
** The following routine is called if the stack overflows.
*/
static void yyStackOverflow(yyParser *yypParser, YYMINORTYPE *yypMinor){
   ParseARG_FETCH;
   yypParser->yyidx--;
#ifndef NDEBUG
   if( yyTraceFILE ){
     fprintf(yyTraceFILE,"%sStack Overflow!\n",yyTracePrompt);
   }
#endif
   while( yypParser->yyidx>=0 ) yy_pop_parser_stack(yypParser);
   /* Here code is inserted which will execute if the parser
   ** stack every overflows */
#line 37 "ltsmin-grammar.lemon"

    (void)yypMinor;
    Abort("stack overflow");
#line 755 "ltsmin-grammar.c"
   ParseARG_STORE; /* Suppress warning about unused %extra_argument var */
}

/*
** Perform a shift action.
*/
static void yy_shift(
  yyParser *yypParser,          /* The parser to be shifted */
  int yyNewState,               /* The new state to shift in */
  int yyMajor,                  /* The major token to shift in */
  YYMINORTYPE *yypMinor         /* Pointer to the minor token to shift in */
){
  yyStackEntry *yytos;
  yypParser->yyidx++;
#ifdef YYTRACKMAXSTACKDEPTH
  if( yypParser->yyidx>yypParser->yyidxMax ){
    yypParser->yyidxMax = yypParser->yyidx;
  }
#endif
#if YYSTACKDEPTH>0 
  if( yypParser->yyidx>=YYSTACKDEPTH ){
    yyStackOverflow(yypParser, yypMinor);
    return;
  }
#else
  if( yypParser->yyidx>=yypParser->yystksz ){
    yyGrowStack(yypParser);
    if( yypParser->yyidx>=yypParser->yystksz ){
      yyStackOverflow(yypParser, yypMinor);
      return;
    }
  }
#endif
  yytos = &yypParser->yystack[yypParser->yyidx];
  yytos->stateno = (YYACTIONTYPE)yyNewState;
  yytos->major = (YYCODETYPE)yyMajor;
  yytos->minor = *yypMinor;
#ifndef NDEBUG
  if( yyTraceFILE && yypParser->yyidx>0 ){
    int i;
    fprintf(yyTraceFILE,"%sShift %d\n",yyTracePrompt,yyNewState);
    fprintf(yyTraceFILE,"%sStack:",yyTracePrompt);
    for(i=1; i<=yypParser->yyidx; i++)
      fprintf(yyTraceFILE," %s",yyTokenName[yypParser->yystack[i].major]);
    fprintf(yyTraceFILE,"\n");
  }
#endif
}

/* The following table contains information about every rule that
** is used during the reduce.
*/
static const struct {
  YYCODETYPE lhs;         /* Symbol on the left-hand side of the rule */
  unsigned char nrhs;     /* Number of right-hand side symbols in the rule */
} yyRuleInfo[] = {
  { 68, 2 },
  { 68, 1 },
  { 69, 2 },
  { 69, 2 },
  { 69, 2 },
  { 69, 2 },
  { 69, 2 },
  { 69, 1 },
  { 70, 5 },
  { 71, 5 },
  { 72, 5 },
  { 77, 0 },
  { 77, 2 },
  { 77, 2 },
  { 76, 0 },
  { 76, 4 },
  { 75, 5 },
  { 78, 1 },
  { 78, 2 },
  { 73, 5 },
  { 80, 1 },
  { 74, 5 },
  { 81, 3 },
  { 81, 2 },
  { 81, 4 },
  { 82, 0 },
  { 82, 2 },
  { 82, 2 },
  { 83, 1 },
  { 83, 1 },
  { 79, 0 },
  { 79, 3 },
  { 84, 0 },
  { 84, 2 },
  { 84, 4 },
  { 84, 2 },
  { 84, 2 },
  { 68, 2 },
  { 85, 3 },
  { 85, 1 },
  { 85, 1 },
  { 85, 1 },
  { 85, 1 },
  { 85, 1 },
  { 85, 1 },
  { 85, 3 },
  { 85, 3 },
  { 85, 3 },
  { 85, 3 },
  { 85, 3 },
  { 85, 3 },
  { 85, 3 },
  { 85, 3 },
  { 85, 3 },
  { 85, 3 },
  { 85, 3 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 2 },
  { 85, 4 },
  { 85, 4 },
  { 85, 4 },
  { 85, 4 },
  { 85, 4 },
  { 85, 4 },
  { 85, 4 },
};

static void yy_accept(yyParser*);  /* Forward Declaration */

/*
** Perform a reduce action and the shift that must immediately
** follow the reduce.
*/
static void yy_reduce(
  yyParser *yypParser,         /* The parser */
  int yyruleno                 /* Number of the rule by which to reduce */
){
  int yygoto;                     /* The next state */
  int yyact;                      /* The next action */
  YYMINORTYPE yygotominor;        /* The LHS of the rule reduced */
  yyStackEntry *yymsp;            /* The top of the parser's stack */
  int yysize;                     /* Amount to pop the stack */
  ParseARG_FETCH;
  yymsp = &yypParser->yystack[yypParser->yyidx];
#ifndef NDEBUG
  if( yyTraceFILE && yyruleno>=0 
        && yyruleno<(int)(sizeof(yyRuleName)/sizeof(yyRuleName[0])) ){
    fprintf(yyTraceFILE, "%sReduce [%s].\n", yyTracePrompt,
      yyRuleName[yyruleno]);
  }
#endif /* NDEBUG */

  /* Silence complaints from purify about yygotominor being uninitialized
  ** in some cases when it is copied into the stack after the following
  ** switch.  yygotominor is uninitialized when a rule reduces that does
  ** not set the value of its left-hand side nonterminal.  Leaving the
  ** value of the nonterminal uninitialized is utterly harmless as long
  ** as the value is never used.  So really the only thing this code
  ** accomplishes is to quieten purify.  
  **
  ** 2007-01-16:  The wireshark project (www.wireshark.org) reports that
  ** without this code, their parser segfaults.  I'm not sure what there
  ** parser is doing to make this happen.  This is the second bug report
  ** from wireshark this week.  Clearly they are stressing Lemon in ways
  ** that it has not been previously stressed...  (SQLite ticket #2172)
  */
  /*memset(&yygotominor, 0, sizeof(yygotominor));*/
  yygotominor = yyzerominor;


  switch( yyruleno ){
  /* Beginning here are the reduction cases.  A typical example
  ** follows:
  **   case 0:
  **  #line <lineno> <grammarfile>
  **     { ... }           // User supplied code
  **  #line <lineno> <thisfile>
  **     break;
  */
      case 0: /* input ::= ETF etf_spec */
#line 47 "ltsmin-grammar.lemon"
{
    Warning(infoLong,"parsing finished");
    etf_model_t model=env->etf;
    lts_type_set_state_label_count(model->ltstype,model->map_count);
    for(int i=0;i<model->map_count;i++){
        lts_type_set_state_label_name(model->ltstype,i,model->map_names[i]);
        lts_type_set_state_label_type(model->ltstype,i,model->map_types[i]);
    }
    Warning(debug,"ETF model has %d transition sections",model->trans_count);
    Warning(debug,"ETF model has %d map sections",model->map_count);
    Warning(debug,"ETF model has %d types",lts_type_get_type_count(model->ltstype));
}
#line 961 "ltsmin-grammar.c"
        break;
      case 1: /* input ::= ERROR */
#line 59 "ltsmin-grammar.lemon"
{
    Abort("The error token is meant to give the lexer a way of passing the error.");
}
#line 968 "ltsmin-grammar.c"
        break;
      case 2: /* etf_spec ::= state_section edge_section */
      case 3: /* etf_spec ::= etf_spec init_section */
      case 4: /* etf_spec ::= etf_spec trans_section */
      case 5: /* etf_spec ::= etf_spec map_section */
      case 6: /* etf_spec ::= etf_spec sort_section */
#line 63 "ltsmin-grammar.lemon"
{
}
#line 978 "ltsmin-grammar.c"
        break;
      case 7: /* etf_spec ::= error */
#line 69 "ltsmin-grammar.lemon"
{
    HREprintf (error, "ETF syntax error.  For a description of the ETF syntax, "
                      "refer to the etf(5) man page.\n");
    HREabort(LTSMIN_EXIT_FAILURE);
}
#line 987 "ltsmin-grammar.c"
        break;
      case 8: /* state_section ::= BEGIN STATE decl_list END STATE */
#line 75 "ltsmin-grammar.lemon"
{
    int N=ETFlistLength(yymsp[-2].minor.yy130);
    if (N==0) {
        Abort("state vector length must be at least 1");
    }
    Warning(infoLong,"The state length is %d",N);
    lts_type_set_state_length(env->etf->ltstype,N);
    etf_list_t list=yymsp[-2].minor.yy130;
    for(int i=N-1;i>=0;i--){
        if (list->fst!=SI_INDEX_FAILED) {
            char *name=SIget(env->idents,list->fst);
            lts_type_set_state_name(env->etf->ltstype,i,name);
        }
        if (list->snd!=SI_INDEX_FAILED) {
            char*sort=SIget(env->idents,list->snd);
            int typeno=ETFgetType(env->etf,sort);
            lts_type_set_state_typeno(env->etf->ltstype,i,typeno);
        }
        list=list->prev;
    }
    ETFlistFree(yymsp[-2].minor.yy130);
    Warning(infoLong,"done");
}
#line 1014 "ltsmin-grammar.c"
        break;
      case 9: /* edge_section ::= BEGIN EDGE decl_list END EDGE */
#line 100 "ltsmin-grammar.lemon"
{
    int N=ETFlistLength(yymsp[-2].minor.yy130);
    Warning(infoLong,"There are %d edge labels",N);
    lts_type_set_edge_label_count(env->etf->ltstype,N);
    etf_list_t list=yymsp[-2].minor.yy130;
    for(int i=N-1;i>=0;i--){
        char *name=SIget(env->idents,list->fst);
        lts_type_set_edge_label_name(env->etf->ltstype,i,name);
        char*sort=SIget(env->idents,list->snd);
        int typeno=ETFgetType(env->etf,sort);
        lts_type_set_edge_label_typeno(env->etf->ltstype,i,typeno);
        list=list->prev;
    }
    ETFlistFree(yymsp[-2].minor.yy130);
    Warning(infoLong,"done");
}
#line 1034 "ltsmin-grammar.c"
        break;
      case 10: /* init_section ::= BEGIN INIT valref_list END INIT */
#line 118 "ltsmin-grammar.lemon"
{
    int N=ETFlistLength(yymsp[-2].minor.yy130);
    if (N!=lts_type_get_state_length(env->etf->ltstype)){
        Abort("incorrect length of initial state: %d instead of %d.",
            N,lts_type_get_state_length(env->etf->ltstype));
    }
    if (env->etf->initial_state) Abort("more than one init section");
    env->etf->initial_state=(int*)RTmalloc(N*sizeof(int));
    etf_list_t list=yymsp[-2].minor.yy130;
    for(int i=N-1;i>=0;i--){
        switch(list->fst){
            case REFERENCE_VALUE:
                env->etf->initial_state[i]=list->snd;
                break;
            case INLINE_VALUE: {
                char *val=SIget(env->idents,list->snd);
                int typeno=lts_type_get_state_typeno(env->etf->ltstype,i);
                env->etf->initial_state[i]=SIput(env->etf->type_values[typeno],val);
                break;
            }
            default:
                Abort("unknown discriminator %d",list->fst);
        }
	list=list->prev;
    }
    ETFlistFree(yymsp[-2].minor.yy130);
    Warning(infoLong,"initial state found");
}
#line 1066 "ltsmin-grammar.c"
        break;
      case 11: /* valref_list ::= */
      case 32: /* step_list ::= */
#line 150 "ltsmin-grammar.lemon"
{yygotominor.yy130=NULL;}
#line 1072 "ltsmin-grammar.c"
        break;
      case 12: /* valref_list ::= valref_list NUMBER */
      case 35: /* step_list ::= step_list NUMBER */
#line 151 "ltsmin-grammar.lemon"
{ yygotominor.yy130=ETFlistAppend(yymsp[-1].minor.yy130,REFERENCE_VALUE,yymsp[0].minor.yy0); }
#line 1078 "ltsmin-grammar.c"
        break;
      case 13: /* valref_list ::= valref_list STRING */
      case 36: /* step_list ::= step_list VALUE */
#line 152 "ltsmin-grammar.lemon"
{ yygotominor.yy130=ETFlistAppend(yymsp[-1].minor.yy130,INLINE_VALUE,yymsp[0].minor.yy0); }
#line 1084 "ltsmin-grammar.c"
        break;
      case 14: /* decl_list ::= */
      case 25: /* map_entry ::= */
#line 157 "ltsmin-grammar.lemon"
{ yygotominor.yy130=NULL; }
#line 1090 "ltsmin-grammar.c"
        break;
      case 15: /* decl_list ::= decl_list IDENT COLON IDENT */
#line 158 "ltsmin-grammar.lemon"
{ yygotominor.yy130=ETFlistAppend(yymsp[-3].minor.yy130,yymsp[-2].minor.yy0,yymsp[0].minor.yy0); }
#line 1095 "ltsmin-grammar.c"
        break;
      case 16: /* sort_section ::= BEGIN SORT sort_list END SORT */
#line 162 "ltsmin-grammar.lemon"
{
    Warning(infoLong,"read %d values",SIgetCount(yymsp[-2].minor.yy138));
}
#line 1102 "ltsmin-grammar.c"
        break;
      case 17: /* sort_list ::= IDENT */
#line 166 "ltsmin-grammar.lemon"
{
    char *name=SIget(env->idents,yymsp[0].minor.yy0);
    Warning(infoLong,"reading values for sort %s",name);
    int typeno=ETFgetType(env->etf,name);
    yygotominor.yy138=env->etf->type_values[typeno];
    if (SIgetCount(yygotominor.yy138)!=0) {
        Abort("sort %s not empty",name);
    }
}
#line 1115 "ltsmin-grammar.c"
        break;
      case 18: /* sort_list ::= sort_list VALUE */
#line 175 "ltsmin-grammar.lemon"
{
    yygotominor.yy138=yymsp[-1].minor.yy138;
    chunk c;
    c.data=SIgetC(env->values,yymsp[0].minor.yy0,(int*)&c.len);
    int idx=SIgetCount(yygotominor.yy138);
    if (idx!=SIputC(yygotominor.yy138,c.data,c.len)) {
	Abort("non-sequential index");
    }
}
#line 1128 "ltsmin-grammar.c"
        break;
      case 19: /* trans_section ::= BEGIN TRANS trans_list end TRANS */
#line 187 "ltsmin-grammar.lemon"
{
    if (ETFrelCount(yymsp[-2].minor.yy153)){
        ensure_access(env->etf->trans_manager,env->etf->trans_count);
        env->etf->trans[env->etf->trans_count]=yymsp[-2].minor.yy153;
        env->etf->trans_count++;
    } else {
        Warning(infoLong,"skipping empty trans section");
    }
}
#line 1141 "ltsmin-grammar.c"
        break;
      case 20: /* end ::= END */
#line 197 "ltsmin-grammar.lemon"
{ env->linebased=0; }
#line 1146 "ltsmin-grammar.c"
        break;
      case 21: /* map_section ::= BEGIN MAP map_list end MAP */
#line 201 "ltsmin-grammar.lemon"
{
    env->etf->map[env->etf->map_count]=yymsp[-2].minor.yy88;
    char*name=env->etf->map_names[env->etf->map_count];
    char*sort=env->etf->map_types[env->etf->map_count];
    //int typeno=ETFgetType(env->etf,sort);
    Warning(infoLong,"added map %d (%s:%s) with %d entries",
            env->etf->map_count,name,sort,ETFmapCount(yymsp[-2].minor.yy88));
    env->etf->map_count++;
    env->etf_current_idx=NULL;
    env->linebased=0;
}
#line 1161 "ltsmin-grammar.c"
        break;
      case 22: /* map_list ::= IDENT COLON IDENT */
#line 213 "ltsmin-grammar.lemon"
{
    char *name=SIget(env->idents,yymsp[-2].minor.yy0);
    char *sort=SIget(env->idents,yymsp[0].minor.yy0);
    int typeno=ETFgetType(env->etf,sort);
    ensure_access(env->etf->map_manager,env->etf->map_count);
    env->etf->map_names[env->etf->map_count]=strdup(name);
    env->etf->map_types[env->etf->map_count]=strdup(sort);
    yygotominor.yy88=ETFmapCreate(lts_type_get_state_length(env->etf->ltstype));
    env->etf_current_idx=env->etf->type_values[typeno];
    env->linebased=1;
}
#line 1176 "ltsmin-grammar.c"
        break;
      case 23: /* map_list ::= map_list END_OF_LINE */
#line 225 "ltsmin-grammar.lemon"
{ yygotominor.yy88=yymsp[-1].minor.yy88; }
#line 1181 "ltsmin-grammar.c"
        break;
      case 24: /* map_list ::= map_list map_entry value END_OF_LINE */
#line 227 "ltsmin-grammar.lemon"
{
    int N=ETFlistLength(yymsp[-2].minor.yy130);
    if(N!=lts_type_get_state_length(env->etf->ltstype)) {
        Abort("bad state length in map entry");
    }
    int state[N];
    etf_list_t list=yymsp[-2].minor.yy130;
    for(int i=N-1;i>=0;i--){
        state[i]=list->fst;
        list=list->prev;
    }
    ETFlistFree(yymsp[-2].minor.yy130);
    ETFmapAdd(yymsp[-3].minor.yy88,state,yymsp[-1].minor.yy64);
    yygotominor.yy88=yymsp[-3].minor.yy88;
}
#line 1200 "ltsmin-grammar.c"
        break;
      case 26: /* map_entry ::= map_entry NUMBER */
#line 247 "ltsmin-grammar.lemon"
{yygotominor.yy130=ETFlistAppend(yymsp[-1].minor.yy130,yymsp[0].minor.yy0+1,0); }
#line 1205 "ltsmin-grammar.c"
        break;
      case 27: /* map_entry ::= map_entry STAR */
#line 248 "ltsmin-grammar.lemon"
{yygotominor.yy130=ETFlistAppend(yymsp[-1].minor.yy130,0,0);}
#line 1210 "ltsmin-grammar.c"
        break;
      case 28: /* value ::= NUMBER */
#line 252 "ltsmin-grammar.lemon"
{ yygotominor.yy64=yymsp[0].minor.yy0; }
#line 1215 "ltsmin-grammar.c"
        break;
      case 29: /* value ::= VALUE */
#line 253 "ltsmin-grammar.lemon"
{
    chunk c;
    c.data=SIgetC(env->values,yymsp[0].minor.yy0,(int*)&c.len);
    yygotominor.yy64=SIputC(env->etf_current_idx,c.data,c.len);
}
#line 1224 "ltsmin-grammar.c"
        break;
      case 30: /* trans_list ::= */
#line 258 "ltsmin-grammar.lemon"
{
    yygotominor.yy153=ETFrelCreate(lts_type_get_state_length(env->etf->ltstype),
                   lts_type_get_edge_label_count(env->etf->ltstype));
    env->linebased=1;
}
#line 1233 "ltsmin-grammar.c"
        break;
      case 31: /* trans_list ::= trans_list step_list END_OF_LINE */
#line 263 "ltsmin-grammar.lemon"
{
    yygotominor.yy153=yymsp[-2].minor.yy153;
    int len=ETFlistLength(yymsp[-1].minor.yy130);
    if(len){
        int N=lts_type_get_state_length(env->etf->ltstype);
        int K=lts_type_get_edge_label_count(env->etf->ltstype);
        if(len!=N+K){
            Abort("bad length in trans entry: %d",len);
        }
        int src[N];
        int dst[N];
        int lbl[K];
        etf_list_t list=yymsp[-1].minor.yy130;
        for(int i=K-1;i>=0;i--){
            switch(list->fst){
                case REFERENCE_VALUE:
                    lbl[i]=list->snd;
                    break;
                case INLINE_VALUE: {
                    chunk c;
                    c.data=SIgetC(env->values,list->snd,(int*)&c.len);
                    int typeno=lts_type_get_edge_label_typeno(env->etf->ltstype,i);
                    lbl[i]=SIputC(env->etf->type_values[typeno],c.data ,c.len);
                    break;
                }
                default:
                    Abort("unknown discriminator %d",list->fst);
            }
            list=list->prev;
        }
        for(int i=N-1;i>=0;i--){
            src[i]=list->fst;
            dst[i]=list->snd;
            list=list->prev;
        }
        ETFlistFree(yymsp[-1].minor.yy130);
        ETFrelAdd(yygotominor.yy153,src,dst,lbl);
    }
}
#line 1276 "ltsmin-grammar.c"
        break;
      case 33: /* step_list ::= step_list STAR */
#line 307 "ltsmin-grammar.lemon"
{ yygotominor.yy130=ETFlistAppend(yymsp[-1].minor.yy130,0,0); }
#line 1281 "ltsmin-grammar.c"
        break;
      case 34: /* step_list ::= step_list NUMBER SLASH NUMBER */
#line 308 "ltsmin-grammar.lemon"
{yygotominor.yy130=ETFlistAppend(yymsp[-3].minor.yy130,yymsp[-2].minor.yy0+1,yymsp[0].minor.yy0+1);}
#line 1286 "ltsmin-grammar.c"
        break;
      case 37: /* input ::= EXPR expr */
#line 326 "ltsmin-grammar.lemon"
{
    (void)yymsp[0].minor.yy125;
    env->expr=yymsp[0].minor.yy125;
}
#line 1294 "ltsmin-grammar.c"
        break;
      case 38: /* expr ::= LPAR expr RPAR */
#line 363 "ltsmin-grammar.lemon"
{ yygotominor.yy125=yymsp[-1].minor.yy125; }
#line 1299 "ltsmin-grammar.c"
        break;
      case 39: /* expr ::= STATE_VAR */
#line 364 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(SVAR, SVAR, yymsp[0].minor.yy0, NULL, NULL);
}
#line 1306 "ltsmin-grammar.c"
        break;
      case 40: /* expr ::= IDENT */
#line 367 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(VAR, VAR, yymsp[0].minor.yy0, NULL, NULL);
}
#line 1313 "ltsmin-grammar.c"
        break;
      case 41: /* expr ::= EDGE_VAR */
#line 370 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(EVAR, EVAR, yymsp[0].minor.yy0, NULL, NULL);
}
#line 1320 "ltsmin-grammar.c"
        break;
      case 42: /* expr ::= VALUE */
#line 373 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(CHUNK, CHUNK, yymsp[0].minor.yy0, NULL, NULL);
}
#line 1327 "ltsmin-grammar.c"
        break;
      case 43: /* expr ::= NUMBER */
#line 376 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(INT, INT, yymsp[0].minor.yy0, NULL, NULL);
}
#line 1334 "ltsmin-grammar.c"
        break;
      case 44: /* expr ::= CONSTANT */
#line 379 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(CONSTANT, LTSminConstantToken(env, yymsp[0].minor.yy0), yymsp[0].minor.yy0, NULL, NULL);
}
#line 1341 "ltsmin-grammar.c"
        break;
      case 45: /* expr ::= expr BIN1 expr */
      case 46: /* expr ::= expr BIN2 expr */
      case 47: /* expr ::= expr BIN3 expr */
      case 48: /* expr ::= expr BIN4 expr */
      case 49: /* expr ::= expr BIN5 expr */
      case 50: /* expr ::= expr BIN6 expr */
      case 51: /* expr ::= expr BIN7 expr */
      case 52: /* expr ::= expr BIN8 expr */
      case 53: /* expr ::= expr BIN9 expr */
      case 54: /* expr ::= expr BIN10 expr */
      case 55: /* expr ::= expr BIN11 expr */
#line 383 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(BINARY_OP, LTSminBinaryToken(env, yymsp[-1].minor.yy0), yymsp[-1].minor.yy0, yymsp[-2].minor.yy125, yymsp[0].minor.yy125);
}
#line 1358 "ltsmin-grammar.c"
        break;
      case 56: /* expr ::= PREFIX1 expr */
      case 57: /* expr ::= PREFIX2 expr */
      case 58: /* expr ::= PREFIX3 expr */
      case 59: /* expr ::= PREFIX4 expr */
      case 60: /* expr ::= PREFIX5 expr */
      case 61: /* expr ::= PREFIX6 expr */
      case 62: /* expr ::= PREFIX7 expr */
      case 63: /* expr ::= PREFIX8 expr */
      case 64: /* expr ::= PREFIX9 expr */
#line 417 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(UNARY_OP, LTSminUnaryToken(env, yymsp[-1].minor.yy0), yymsp[-1].minor.yy0, yymsp[0].minor.yy125, NULL);
}
#line 1373 "ltsmin-grammar.c"
        break;
      case 65: /* expr ::= expr POSTFIX1 */
      case 66: /* expr ::= expr POSTFIX2 */
      case 67: /* expr ::= expr POSTFIX3 */
      case 68: /* expr ::= expr POSTFIX4 */
      case 69: /* expr ::= expr POSTFIX5 */
      case 70: /* expr ::= expr POSTFIX6 */
      case 71: /* expr ::= expr POSTFIX7 */
      case 72: /* expr ::= expr POSTFIX8 */
      case 73: /* expr ::= expr POSTFIX9 */
#line 451 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(UNARY_OP, LTSminUnaryToken(env, yymsp[0].minor.yy0), yymsp[0].minor.yy0, yymsp[-1].minor.yy125, NULL);
}
#line 1388 "ltsmin-grammar.c"
        break;
      case 74: /* expr ::= MU_SYM IDENT DOT expr */
#line 482 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(MU_FIX, yymsp[-3].minor.yy0, yymsp[-2].minor.yy0, yymsp[0].minor.yy125, NULL);
}
#line 1395 "ltsmin-grammar.c"
        break;
      case 75: /* expr ::= NU_SYM IDENT DOT expr */
#line 486 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(NU_FIX, yymsp[-3].minor.yy0, yymsp[-2].minor.yy0, yymsp[0].minor.yy125, NULL);
}
#line 1402 "ltsmin-grammar.c"
        break;
      case 76: /* expr ::= EXISTS_SYM expr DOT expr */
#line 490 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(EXISTS_STEP, yymsp[-3].minor.yy0, 0, yymsp[-2].minor.yy125, yymsp[0].minor.yy125);
}
#line 1409 "ltsmin-grammar.c"
        break;
      case 77: /* expr ::= ALL_SYM expr DOT expr */
#line 494 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(FORALL_STEP, yymsp[-3].minor.yy0, 0, yymsp[-2].minor.yy125, yymsp[0].minor.yy125);
}
#line 1416 "ltsmin-grammar.c"
        break;
      case 78: /* expr ::= IF IDENT THEN expr */
#line 498 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = yymsp[0].minor.yy125 ;
}
#line 1423 "ltsmin-grammar.c"
        break;
      case 79: /* expr ::= EDGE_EXIST_LEFT EDGE_VAR EDGE_EXIST_RIGHT expr */
#line 502 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(EDGE_EXIST, EDGE_EXIST, yymsp[-2].minor.yy0, yymsp[0].minor.yy125, NULL);
}
#line 1430 "ltsmin-grammar.c"
        break;
      case 80: /* expr ::= EDGE_ALL_LEFT EDGE_VAR EDGE_ALL_RIGHT expr */
#line 506 "ltsmin-grammar.lemon"
{
    yygotominor.yy125 = LTSminExpr(EDGE_ALL, EDGE_ALL, yymsp[-2].minor.yy0, yymsp[0].minor.yy125, NULL);
}
#line 1437 "ltsmin-grammar.c"
        break;
  };
  yygoto = yyRuleInfo[yyruleno].lhs;
  yysize = yyRuleInfo[yyruleno].nrhs;
  yypParser->yyidx -= yysize;
  yyact = yy_find_reduce_action(yymsp[-yysize].stateno,(YYCODETYPE)yygoto);
  if( yyact < YYNSTATE ){
#ifdef NDEBUG
    /* If we are not debugging and the reduce action popped at least
    ** one element off the stack, then we can push the new element back
    ** onto the stack here, and skip the stack overflow test in yy_shift().
    ** That gives a significant speed improvement. */
    if( yysize ){
      yypParser->yyidx++;
      yymsp -= yysize-1;
      yymsp->stateno = (YYACTIONTYPE)yyact;
      yymsp->major = (YYCODETYPE)yygoto;
      yymsp->minor = yygotominor;
    }else
#endif
    {
      yy_shift(yypParser,yyact,yygoto,&yygotominor);
    }
  }else{
    assert( yyact == YYNSTATE + YYNRULE + 1 );
    yy_accept(yypParser);
  }
}

/*
** The following code executes when the parse fails
*/
static void yy_parse_failed(
  yyParser *yypParser           /* The parser */
){
  ParseARG_FETCH;
#ifndef NDEBUG
  if( yyTraceFILE ){
    fprintf(yyTraceFILE,"%sFail!\n",yyTracePrompt);
  }
#endif
  while( yypParser->yyidx>=0 ) yy_pop_parser_stack(yypParser);
  /* Here code is inserted which will be executed whenever the
  ** parser fails */
#line 34 "ltsmin-grammar.lemon"
 HREabort(LTSMIN_EXIT_FAILURE); 
#line 1484 "ltsmin-grammar.c"
  ParseARG_STORE; /* Suppress warning about unused %extra_argument variable */
}

/*
** The following code executes when a syntax error first occurs.
*/
static void yy_syntax_error(
  yyParser *yypParser,           /* The parser */
  int yymajor,                   /* The major type of the error token */
  YYMINORTYPE yyminor            /* The minor type of the error token */
){
  ParseARG_FETCH;
#define TOKEN (yyminor.yy0)
#line 26 "ltsmin-grammar.lemon"

    (void)yymajor;(void)yyminor;
    if (env->lineno == 0) {
        HREmessage(error,"syntax error near pos %d",env->linepos+1);
    } else {
        HREmessage(error,"syntax error near line %d, pos %d",env->lineno+1,env->linepos+1);
    }
#line 1506 "ltsmin-grammar.c"
  ParseARG_STORE; /* Suppress warning about unused %extra_argument variable */
}

/*
** The following is executed when the parser accepts
*/
static void yy_accept(
  yyParser *yypParser           /* The parser */
){
  ParseARG_FETCH;
#ifndef NDEBUG
  if( yyTraceFILE ){
    fprintf(yyTraceFILE,"%sAccept!\n",yyTracePrompt);
  }
#endif
  while( yypParser->yyidx>=0 ) yy_pop_parser_stack(yypParser);
  /* Here code is inserted which will be executed whenever the
  ** parser accepts */
#line 35 "ltsmin-grammar.lemon"
 Print1(infoLong,"success!"); 
#line 1527 "ltsmin-grammar.c"
  ParseARG_STORE; /* Suppress warning about unused %extra_argument variable */
}

/* The main parser program.
** The first argument is a pointer to a structure obtained from
** "ParseAlloc" which describes the current state of the parser.
** The second argument is the major token number.  The third is
** the minor token.  The fourth optional argument is whatever the
** user wants (and specified in the grammar) and is available for
** use by the action routines.
**
** Inputs:
** <ul>
** <li> A pointer to the parser (an opaque structure.)
** <li> The major token number.
** <li> The minor token number.
** <li> An option argument of a grammar-specified type.
** </ul>
**
** Outputs:
** None.
*/
void Parse(
  void *yyp,                   /* The parser */
  int yymajor,                 /* The major token code number */
  ParseTOKENTYPE yyminor       /* The value for the token */
  ParseARG_PDECL               /* Optional %extra_argument parameter */
){
  YYMINORTYPE yyminorunion;
  int yyact;            /* The parser action. */
  int yyendofinput;     /* True if we are at the end of input */
#ifdef YYERRORSYMBOL
  int yyerrorhit = 0;   /* True if yymajor has invoked an error */
#endif
  yyParser *yypParser;  /* The parser */

  /* (re)initialize the parser, if necessary */
  yypParser = (yyParser*)yyp;
  if( yypParser->yyidx<0 ){
#if YYSTACKDEPTH<=0
    if( yypParser->yystksz <=0 ){
      /*memset(&yyminorunion, 0, sizeof(yyminorunion));*/
      yyminorunion = yyzerominor;
      yyStackOverflow(yypParser, &yyminorunion);
      return;
    }
#endif
    yypParser->yyidx = 0;
    yypParser->yyerrcnt = -1;
    yypParser->yystack[0].stateno = 0;
    yypParser->yystack[0].major = 0;
  }
  yyminorunion.yy0 = yyminor;
  yyendofinput = (yymajor==0);
  ParseARG_STORE;

#ifndef NDEBUG
  if( yyTraceFILE ){
    fprintf(yyTraceFILE,"%sInput %s\n",yyTracePrompt,yyTokenName[yymajor]);
  }
#endif

  do{
    yyact = yy_find_shift_action(yypParser,(YYCODETYPE)yymajor);
    if( yyact<YYNSTATE ){
      assert( !yyendofinput );  /* Impossible to shift the $ token */
      yy_shift(yypParser,yyact,yymajor,&yyminorunion);
      yypParser->yyerrcnt--;
      yymajor = YYNOCODE;
    }else if( yyact < YYNSTATE + YYNRULE ){
      yy_reduce(yypParser,yyact-YYNSTATE);
    }else{
      assert( yyact == YY_ERROR_ACTION );
#ifdef YYERRORSYMBOL
      int yymx;
#endif
#ifndef NDEBUG
      if( yyTraceFILE ){
        fprintf(yyTraceFILE,"%sSyntax Error!\n",yyTracePrompt);
      }
#endif
#ifdef YYERRORSYMBOL
      /* A syntax error has occurred.
      ** The response to an error depends upon whether or not the
      ** grammar defines an error token "ERROR".  
      **
      ** This is what we do if the grammar does define ERROR:
      **
      **  * Call the %syntax_error function.
      **
      **  * Begin popping the stack until we enter a state where
      **    it is legal to shift the error symbol, then shift
      **    the error symbol.
      **
      **  * Set the error count to three.
      **
      **  * Begin accepting and shifting new tokens.  No new error
      **    processing will occur until three tokens have been
      **    shifted successfully.
      **
      */
      if( yypParser->yyerrcnt<0 ){
        yy_syntax_error(yypParser,yymajor,yyminorunion);
      }
      yymx = yypParser->yystack[yypParser->yyidx].major;
      if( yymx==YYERRORSYMBOL || yyerrorhit ){
#ifndef NDEBUG
        if( yyTraceFILE ){
          fprintf(yyTraceFILE,"%sDiscard input token %s\n",
             yyTracePrompt,yyTokenName[yymajor]);
        }
#endif
        yy_destructor(yypParser, (YYCODETYPE)yymajor,&yyminorunion);
        yymajor = YYNOCODE;
      }else{
         while(
          yypParser->yyidx >= 0 &&
          yymx != YYERRORSYMBOL &&
          (yyact = yy_find_reduce_action(
                        yypParser->yystack[yypParser->yyidx].stateno,
                        YYERRORSYMBOL)) >= YYNSTATE
        ){
          yy_pop_parser_stack(yypParser);
        }
        if( yypParser->yyidx < 0 || yymajor==0 ){
          yy_destructor(yypParser,(YYCODETYPE)yymajor,&yyminorunion);
          yy_parse_failed(yypParser);
          yymajor = YYNOCODE;
        }else if( yymx!=YYERRORSYMBOL ){
          YYMINORTYPE u2;
          u2.YYERRSYMDT = 0;
          yy_shift(yypParser,yyact,YYERRORSYMBOL,&u2);
        }
      }
      yypParser->yyerrcnt = 3;
      yyerrorhit = 1;
#else  /* YYERRORSYMBOL is not defined */
      /* This is what we do if the grammar does not define ERROR:
      **
      **  * Report an error message, and throw away the input token.
      **
      **  * If the input token is $, then fail the parse.
      **
      ** As before, subsequent error messages are suppressed until
      ** three input tokens have been successfully shifted.
      */
      if( yypParser->yyerrcnt<=0 ){
        yy_syntax_error(yypParser,yymajor,yyminorunion);
      }
      yypParser->yyerrcnt = 3;
      yy_destructor(yypParser,(YYCODETYPE)yymajor,&yyminorunion);
      if( yyendofinput ){
        yy_parse_failed(yypParser);
      }
      yymajor = YYNOCODE;
#endif
    }
  }while( yymajor!=YYNOCODE && yypParser->yyidx>=0 );
  return;
}
