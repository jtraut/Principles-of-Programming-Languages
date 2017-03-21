/*
 * CSCI 3155: Lab 5 Worksheet
 *
 * This worksheet demonstrates how you could experiment
 * interactively with your implementations in Lab5.scala.
 */

// Imports the ast nodes
import jsy.lab6._
import jsy.lab6.ast._

// Imports all of the functions form jsy.student.Lab2 (your implementations in Lab2.scala)
import jsy.student.Lab6._

// Jsy parser using the reference RegExpr parser.
val refparser = (new JsyParser)

// Jsy parser using the your RegExpr parser.
val yourparser = new JsyParser(REParser.parse)

// Try out the reference RegExpr parser
val re1 = RegExprParser.parse("a")
refparser.parse("/^a$/")

// Try out your RegExpr parser
//REParser.parse("a")
//yourparser.parse("/^a$/")

// Try out your matcher
//retest(re1, "a")