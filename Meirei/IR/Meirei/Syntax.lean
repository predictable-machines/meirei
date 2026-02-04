/-
  Simple Imperative Language Syntax

  This module defines a grammar for a simple imperative language using Lean 4's syntax feature.
  It supports the intSum and mySum examples from Basic.lean.
-/

namespace Meirei

-- Type syntax
declare_syntax_cat imp_type
syntax "int" : imp_type
syntax "[" imp_type "]" : imp_type  -- List types

-- Expression syntax
declare_syntax_cat imp_expr
syntax ident : imp_expr                                    -- Variables
syntax num : imp_expr                                      -- Numbers
syntax "-" num : imp_expr                                  -- Negative numbers
syntax imp_expr "+" imp_expr : imp_expr                    -- Addition
syntax imp_expr "-" imp_expr : imp_expr                    -- Subtraction
syntax imp_expr "*" imp_expr : imp_expr                    -- Multiplication
syntax imp_expr "/" imp_expr : imp_expr                    -- Division
syntax imp_expr ">" imp_expr : imp_expr                    -- Greater than
syntax imp_expr "<" imp_expr : imp_expr                    -- Less than
syntax imp_expr "==" imp_expr : imp_expr                   -- Equality
syntax ident "(" imp_expr,* ")" : imp_expr                 -- Function calls
syntax "(" imp_expr ")" : imp_expr                         -- Parenthesized expressions

-- Statement syntax
declare_syntax_cat imp_stmt
syntax "return" imp_expr ";" : imp_stmt                    -- Return statement
syntax "var" ident ":" imp_type "=" imp_expr ";" : imp_stmt -- Variable declaration
syntax ident "=" imp_expr ";" : imp_stmt                   -- Assignment
syntax ident "(" imp_expr,* ")" ";" : imp_stmt             -- Function call statement (effectful, no result)
syntax ident "<-" ident "(" imp_expr,* ")" ";" : imp_stmt  -- Effectful call with result binding
syntax "for" ident "in" imp_expr "{" imp_stmt* "}" : imp_stmt -- For loop
syntax "if" "(" imp_expr ")" "{" imp_stmt* "}" : imp_stmt  -- If statement
syntax "if" "(" imp_expr ")" "{" imp_stmt* "}" "else" "{" imp_stmt* "}" : imp_stmt  -- If-else statement
syntax "break" ";" : imp_stmt                              -- Break from loop
syntax "{" imp_stmt* "}" : imp_stmt                        -- Block

-- Parameter syntax
declare_syntax_cat imp_param
syntax ident ":" imp_type : imp_param

-- Function definition syntax
declare_syntax_cat imp_fundef
syntax "def" ident "(" imp_param,* ")" ":" imp_type "{" imp_stmt* "}" : imp_fundef

-- Term-level syntax that can be used as expressions
syntax "[Meirei|" imp_fundef "]" : term

end Meirei
