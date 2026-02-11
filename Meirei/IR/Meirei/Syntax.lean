/-
  Simple Imperative Language Syntax

  This module defines a grammar for a simple imperative language using Lean 4's syntax feature.
  It supports the intSum and mySum examples from Basic.lean.
-/

namespace Meirei

-- Type syntax: all types start with uppercase identifiers.
-- Lowercase identifiers are reserved for functions and type constructors.
declare_syntax_cat imp_type
syntax "[" imp_type "]" : imp_type  -- List sugar: [T] → List T
syntax ident : imp_type             -- Named types (Int, String, Point, etc.)
syntax imp_type "?" : imp_type      -- Option sugar: T? → Option T

-- Expression syntax
declare_syntax_cat imp_expr
syntax ident : imp_expr                                    -- Variables
syntax num : imp_expr                                      -- Numbers
syntax "-" num : imp_expr                                  -- Negative numbers
syntax:max str : imp_expr                                  -- String literals
syntax imp_expr "+" imp_expr : imp_expr                    -- Addition
syntax imp_expr "-" imp_expr : imp_expr                    -- Subtraction
syntax imp_expr "*" imp_expr : imp_expr                    -- Multiplication
syntax imp_expr "/" imp_expr : imp_expr                    -- Division
syntax imp_expr ">" imp_expr : imp_expr                    -- Greater than
syntax imp_expr "<" imp_expr : imp_expr                    -- Less than
syntax imp_expr "==" imp_expr : imp_expr                   -- Equality
-- Function call argument: string literals can't appear directly in imp_expr,*
-- due to a Lean parser first-set limitation, so we use a wrapper category.
declare_syntax_cat imp_arg
syntax imp_expr : imp_arg
syntax:max str : imp_arg
syntax ident "(" imp_arg,* ")" : imp_expr                  -- Function calls
syntax "(" imp_expr ")" : imp_expr                         -- Parenthesized expressions
syntax imp_expr "." ident : imp_expr                       -- Field access

-- Statement syntax
declare_syntax_cat imp_stmt
syntax "return" imp_expr ";" : imp_stmt                    -- Return statement
syntax "var" ident ":" imp_type "=" imp_expr ";" : imp_stmt -- Variable declaration
syntax ident "=" imp_expr ";" : imp_stmt                   -- Assignment
syntax ident "(" imp_arg,* ")" ";" : imp_stmt              -- Function call statement (effectful, no result)
syntax ident "<-" ident "(" imp_arg,* ")" ";" : imp_stmt   -- Effectful call with result binding
syntax "for" ident "in" imp_expr "{" imp_stmt* "}" : imp_stmt -- For loop
syntax "if" "(" imp_expr ")" "{" imp_stmt* "}" : imp_stmt  -- If statement
syntax "if" "(" imp_expr ")" "{" imp_stmt* "}" "else" "{" imp_stmt* "}" : imp_stmt  -- If-else statement
syntax "while" "(" imp_expr ")" ("decreasing" "(" imp_expr ")")? "{" imp_stmt* "}" : imp_stmt -- While loop
syntax "break" ";" : imp_stmt                              -- Break from loop
syntax "{" imp_stmt* "}" : imp_stmt                        -- Block

-- Match arm syntax (declared before use in imp_stmt)
declare_syntax_cat imp_match_arm
syntax "case" ident "(" ident,* ")" "{" imp_stmt* "}" : imp_match_arm

syntax "match" imp_expr "{" imp_match_arm* "}" : imp_stmt  -- Match statement

-- Parameter syntax
declare_syntax_cat imp_param
syntax ident ":" imp_type : imp_param

-- Function definition syntax
declare_syntax_cat imp_fundef
syntax "def" ident "(" imp_param,* ")" ":" imp_type "{" imp_stmt* "}" : imp_fundef

-- Term-level syntax that can be used as expressions
syntax "[Meirei|" imp_fundef "]" : term

-- Field definition syntax (for structs and enum constructors)
declare_syntax_cat imp_field_def
syntax ident ":" imp_type : imp_field_def

-- Enum constructor syntax
declare_syntax_cat imp_enum_ctor
syntax ident "(" imp_field_def,* ")" : imp_enum_ctor

-- Struct definition syntax
declare_syntax_cat imp_struct_def
syntax "struct" ident "{" imp_field_def,* "}" : imp_struct_def

-- Enum definition syntax
declare_syntax_cat imp_enum_def
syntax "enum" ident "{" imp_enum_ctor,* "}" : imp_enum_def

-- Command-level syntax for type declarations
syntax "meirei_type" imp_struct_def : command
syntax "meirei_type" imp_enum_def : command

end Meirei
