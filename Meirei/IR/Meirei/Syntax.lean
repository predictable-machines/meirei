/-
  Simple Imperative Language Syntax

  This module defines a grammar for a simple imperative language using Lean 4's syntax feature.
  It supports the intSum and mySum examples from Basic.lean.
-/

namespace Meirei

-- Custom identifier syntax that supports ? and ! suffixes (matching Lean's identifier rules)
-- These must be atomic to prevent whitespace between the base identifier and suffix
declare_syntax_cat imp_ident
syntax ident : imp_ident                    -- Base identifier
syntax atomic(ident "?") : imp_ident       -- Identifier with ? suffix
syntax atomic(ident "!") : imp_ident       -- Identifier with ! suffix

-- Type syntax: all types start with uppercase identifiers.
-- Lowercase identifiers are reserved for functions and type constructors.
declare_syntax_cat imp_type
syntax "[" imp_type "]" : imp_type  -- List sugar: [T] → List T
syntax ident : imp_type             -- Named types (Int, String, Point, etc.)
syntax ident "(" imp_type,* ")" : imp_type  -- Multi-arg type: Except(String, Int)
syntax imp_type "?" : imp_type      -- Option sugar: T? → Option T

-- Expression syntax
declare_syntax_cat imp_expr
syntax imp_ident : imp_expr                                -- Variables (supports ? and ! suffixes)
syntax num : imp_expr                                      -- Numbers
syntax "-" num : imp_expr                                  -- Negative numbers
syntax:max str : imp_expr                                  -- String literals
-- Precedence levels follow standard conventions (matching Lean's infixl pattern):
--   Left operand gets :p, right operand gets :(p+1) for left-associativity.
--   75: unary prefix (!)
--   70: multiplicative (*, /, %)
--   65: additive (+, -)
--   50: comparison (>, <, >=, <=, ==, !=)
--   35: logical AND (&&)
--   30: logical OR (||)
syntax:75 "!" imp_expr:75 : imp_expr                                   -- Logical NOT
syntax:70 imp_expr:70 "*" imp_expr:71 : imp_expr                      -- Multiplication
syntax:70 imp_expr:70 "/" imp_expr:71 : imp_expr                      -- Division
syntax:70 imp_expr:70 "%" imp_expr:71 : imp_expr                      -- Modulo
syntax:65 imp_expr:65 "+" imp_expr:66 : imp_expr                      -- Addition
syntax:65 imp_expr:65 "-" imp_expr:66 : imp_expr                      -- Subtraction
syntax:65 imp_expr:65 "++" imp_expr:66 : imp_expr                     -- String concatenation
syntax:50 imp_expr:50 ">" imp_expr:51 : imp_expr                      -- Greater than
syntax:50 imp_expr:50 "<" imp_expr:51 : imp_expr                      -- Less than
syntax:50 imp_expr:50 ">=" imp_expr:51 : imp_expr                     -- Greater than or equal
syntax:50 imp_expr:50 "<=" imp_expr:51 : imp_expr                     -- Less than or equal
syntax:50 imp_expr:50 "==" imp_expr:51 : imp_expr                     -- Equality
syntax:50 imp_expr:50 "!=" imp_expr:51 : imp_expr                     -- Not equal
syntax:35 imp_expr:35 "&&" imp_expr:36 : imp_expr                     -- Logical AND
syntax:30 imp_expr:30 "||" imp_expr:31 : imp_expr                     -- Logical OR
-- Function call argument: string literals can't appear directly in imp_expr,*
-- due to a Lean parser first-set limitation, so we use a wrapper category.
declare_syntax_cat imp_arg
syntax imp_expr : imp_arg
syntax:max str : imp_arg
syntax imp_ident ("." imp_ident)* "(" imp_arg,* ")" : imp_expr      -- Function calls (qualified names with ? and ! support)
syntax "(" imp_expr ")" : imp_expr                         -- Parenthesized expressions
syntax imp_expr "." imp_ident : imp_expr                   -- Field access (supports ? and ! suffixes)
syntax "[" imp_expr,* "]" : imp_expr                       -- List literal

-- Statement syntax
declare_syntax_cat imp_stmt
syntax "return" imp_expr ";" : imp_stmt                    -- Return statement
syntax "var" ident ":" imp_type "=" imp_expr ";" : imp_stmt -- Variable declaration (new bindings use plain ident)
syntax imp_ident "=" imp_expr ";" : imp_stmt               -- Assignment (references existing variable)
syntax imp_ident ("." imp_ident)* "(" imp_arg,* ")" ";" : imp_stmt              -- Function call statement (supports ? and !)
syntax ident "<-" imp_ident ("." imp_ident)* "(" imp_arg,* ")" ";" : imp_stmt   -- Effectful call with result binding
syntax "for" ident "in" imp_expr "{" imp_stmt* "}" : imp_stmt -- For loop
syntax "if" "(" imp_expr ")" "{" imp_stmt* "}" : imp_stmt  -- If statement
syntax "if" "(" imp_expr ")" "{" imp_stmt* "}" "else" "{" imp_stmt* "}" : imp_stmt  -- If-else statement
syntax "while" "(" imp_expr ")" ("decreasing" "(" imp_expr ")")? "{" imp_stmt* "}" : imp_stmt -- While loop
syntax "break" ";" : imp_stmt                              -- Break from loop
syntax "throw" imp_expr ";" : imp_stmt                     -- Throw expression (in Except-returning functions)
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
syntax "def" imp_ident "(" imp_param,* ")" ":" imp_type "{" imp_stmt* "}" : imp_fundef  -- Function names can have ? or ! suffixes

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
