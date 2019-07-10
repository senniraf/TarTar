#!/usr/bin/python
import sys
import os
import unittest
from pyuppaal.ulp import lexer, selectStatementParser, expressionParser, node

class TestSelectStatementParsing(unittest.TestCase):

    def test_parse_select_int_simple(self):
        pars = selectStatementParser.selectStatementParser("x : int")
        AST = pars.parseSelectStatements()
        self.assertEqual(AST.type, 'SelectStatement')
        self.assertEqual(len(AST.children), 1)
        self.assertEqual(AST.children[0].type.children[0], 'x')
        ident = AST.children[0].children
        self.assertEqual(len(ident.children), 0)
        self.assertEqual(ident.type, 'TypeInt')

    def test_parse_select_noint(self):
        pars = selectStatementParser.selectStatementParser("x : noint")
        with self.assertRaises(KeyError):
            AST = pars.parseSelectStatements()

    def test_parse_select_int_range(self):
        pars = selectStatementParser.selectStatementParser("x : int[0, 1]")
        AST = pars.parseSelectStatements()
        self.assertEqual(AST.type, 'SelectStatement')
        self.assertEqual(len(AST.children), 1)
        self.assertEqual(AST.children[0].type.children[0], 'x')
        ident = AST.children[0].children
        self.assertEqual(len(ident.children), 2)
        self.assertEqual(ident.type, 'TypeInt')


    def test_parse_select_two_variables(self):
        pars = selectStatementParser.selectStatementParser("x : int[0, 1], y : int[0, 1]")
        AST = pars.parseSelectStatements()
        self.assertEqual(AST.type, 'SelectStatement')
        self.assertEqual(len(AST.children), 2)
        self.assertEqual(AST.children[0].type.children[0], 'x')
        self.assertEqual(AST.children[1].type.children[0], 'y')
        ident = AST.children[0].children
        self.assertEqual(len(ident.children), 2)
        self.assertEqual(ident.type, 'TypeInt')
        ident = AST.children[1].children
        self.assertEqual(len(ident.children), 2)
        self.assertEqual(ident.type, 'TypeInt')
 
if __name__ == '__main__':
    unittest.main()
