# ubiquity

[![Build Status](https://travis-ci.org/ralexstokes/ubiquity.svg?branch=master)](https://travis-ci.org/ralexstokes/ubiquity)

# about the language

`ubiquity` is a Lisp language inspired by Clojure.

## syntax

Refer to `parser::lexer::Token` for the possible syntactic elements. In general, the lexer recognizes a number of delimiters and numeric types; all other input is considered a symbol. Given that the `Token::Symbol` type wraps a `&str` from Rust, any valid Rust string (aka UTF-8) is a valid symbol in `ubiquity`.

## grammar

refer to `parser::ast::Ast` for the possible grammatical types.
