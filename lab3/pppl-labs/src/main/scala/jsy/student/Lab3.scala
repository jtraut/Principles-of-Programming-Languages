package jsy.student

import javax.swing.JTree.DynamicUtilTreeNode

object Lab3 extends jsy.util.JsyApplication {
  import jsy.lab3.Parser
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * Jake Traut
   * 
   * Partner: Brian Salmon
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }

  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */
  
  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0.0
      case B(true) => 1.0
      case Undefined => Double.NaN
      case S(s) => try {s.toDouble} catch {case _: NumberFormatException => Double.NaN}
      case Function(_, _, _) => Double.NaN
      case _ => throw new IllegalArgumentException
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => if (n == 0 || n.isNaN()) false else true
      case S(s) => if (s == "") false else true
      case Function(_, _, _) => true
      case Undefined => false
      case _ => throw new IllegalArgumentException
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
        // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
        // of the function (from the input program).
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString()
      case B(b) => if (b) "true" else "false"
      case Function(_, _, _) => "function"
      case Undefined => "undefined"
      case _ => throw new IllegalArgumentException
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1),S(s2)) => (bop: @unchecked) match {
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
      }
      case (v1,v2) => val(n1,n2) = (toNumber(v1), toNumber(v2))
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
      }
      case _ => throw new IllegalArgumentException
    }
  }

  /* Big-Step Interpreter with Dynamic Scoping */
  
  /*
   * This code is a reference implementation of JavaScripty without
   * strings and functions (i.e., Lab 2).  You are to welcome to
   * replace it with your code from Lab 2.
   */
  def eval(env: Env, e: Expr): Expr = {
    def eToN(e: Expr): Double = toNumber(eval(env, e))
    def eToB(e: Expr): Boolean = toBoolean(eval(env, e))
    def eToVal(e: Expr): Expr = eval(env, e)
    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e
      case Var(x) => get(env, x)
      
      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

      case Unary(uop, e) => uop match {
        case Neg => N(-eToN(e))
        case Not => B(!eToB(e))
        case _ => throw new UnsupportedOperationException
      }

      case Binary(bop, e1, e2) => bop match {
        case Plus => (eToVal(e1), eToVal(e2)) match {
          case (S(s1),v2) => S(s1 + toStr(v2))
          case (v1,S(s2)) => S(toStr(v1) + s2)
          case (_, _) => N(eToN(e1) + eToN(e2))
        }
        case Minus => N(eToN(e1) - eToN(e2))
        case Times => N(eToN(e1) * eToN(e2))
        case Div => {
          try {N(eToN(e1) / eToN(e2))} catch {case _: IllegalArgumentException => Undefined }
        }
        case (Lt|Le|Gt|Ge) => B(inequalityVal(bop,eToVal(e1),eToVal(e2)))
        case Eq => (eToVal(e1), eToVal(e2)) match {
          case (Function(_,_,_),_)|(_,Function(_,_,_)) => throw new DynamicTypeError(e)
          case (N(n1),N(n2)) => B(n1 == n2)
          case (B(b1),B(b2)) => B(b1 == b2)
          case (S(s1),S(s2)) => B(s1 == s2)
          case (_,_) => B(false)
        }
        case Ne => (eToVal(e1), eToVal(e2)) match {
          case (Function(_,_,_),_)|(_,Function(_,_,_)) => throw new DynamicTypeError(e)
          case (N(n1),N(n2)) => B(n1 != n2)
          case (B(b1),B(b2)) => B(b1 != b2)
          case (S(s1),S(s2)) => B(s1 != s2)
          case (_,_) => B(true)
        }
        case And => {
          if(!eToB(e1)) eToVal(e1)
          else eToVal(e2)
        }
        case Or => {
          if (eToB(e1)) eToVal(e1)
          else eToVal(e2)
        }
        case Seq => {
          eToVal(e1)
          eToVal(e2)
        }
        case _ => throw new UnsupportedOperationException
      }
      case If(ifE, thenE, elseE) => {
        if(eToB(ifE)) eToVal(thenE)
        else eToVal(elseE)
      }
      case ConstDecl(x, e1, e2) => {
        val boundedEnv = extend(env, x, eToVal(e1))
        eval(boundedEnv, e2)
      }

      case Call(e1,e2) => (eToVal(e1),eToVal(e2)) match {
        case (Function(None,x,ebody),v2) => eval(extend(env,x,v2),ebody)
        case (v1 @ Function(Some(x1),x2,ebody),v2) => eval(extend(extend(env,x2,v2),x1,v1),ebody)
        case (_,_) => throw new DynamicTypeError(e)
      }

      case _ => throw new UnsupportedOperationException
        // ****** Your cases here
    }
  }
    

  /* Small-Step Interpreter with Static Scoping */
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    /* Simple helper that calls substitute on an expression
     * with the input value v and variable name x. */
    def subst(e: Expr): Expr = substitute(e, v, x)
    /* Body */
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Var(y) => if (x==y) v else Var(y)
      case Print(e1) => Print(subst(e1))
      case Function(None,y,e1) => if (x==y) e else Function(None,y,subst(e1))
      case Function(Some(z),y,e1) => {
        if (x==y || x==z) e
        else Function(Some(z),y,subst(e1))
      }
      case Unary(uop,e1) => Unary(uop,subst(e1))
      case Binary(bop,e1,e2) => Binary(bop,subst(e1),subst(e2))
      case If(ifE,thenE,elseE) => If(subst(ifE),subst(thenE),subst(elseE))
      case ConstDecl(y,e1,e2) => ConstDecl(y,subst(e1),(if(x==y) e2 else subst(e2)))
      case Call(e1,e2) => Call(subst(e1),subst(e2))
      case _ => throw new UnsupportedOperationException
    }
  }
    
  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      
        // ****** Your cases here
      case Unary(uop,v1) if isValue(v1) => uop match {
        case Neg => N(-toNumber(v1))
        case Not => B(!toBoolean(v1))
      }
      case Binary(Seq,v1,e2) if isValue(v1) => e2
      case Binary(Plus,S(s1),v2) if isValue(v2) => S(s1+toStr(v2))
      case Binary(Plus,v1,S(s2)) if isValue(v1) => S(toStr(v1)+s2)
      case Binary(bop @ (Lt|Le|Gt|Ge),S(s1),S(s2)) => B(inequalityVal(bop,S(s1),S(s2)))
      case Binary(And,v1,e2) if isValue(v1) => if(!toBoolean(v1)) v1 else e2
      case Binary(Or,v1,e2) if isValue(v1) => if(toBoolean(v1)) v1 else e2
      case Binary(bop,v1,v2) if (isValue(v1) && isValue(v2)) => bop match {
        case Plus => N(toNumber(v1) + toNumber(v2))
        case Minus => N(toNumber(v1) - toNumber(v2))
        case Times => N(toNumber(v1) * toNumber(v2))
        case Div => {
          try {N(toNumber(v1) / toNumber(v2))} catch {case _: IllegalArgumentException => Undefined }
        }
        case (Lt|Le|Gt|Ge) => B(inequalityVal(bop,v1,v2))
        case Eq => (v1,v2) match {
          case (Function(_,_,_),_)|(_,Function(_,_,_)) => throw new DynamicTypeError(e)
          case (N(n1),N(n2)) => B(n1 == n2)
          case (B(b1),B(b2)) => B(b1 == b2)
          case (S(s1),S(s2)) => B(s1 == s2)
          case (_,_) => B(toNumber(v1) == toNumber(v2))
        }
        case Ne => (v1,v2) match {
          case (Function(_,_,_),_)|(_,Function(_,_,_)) => throw new DynamicTypeError(e)
          case (N(n1),N(n2)) => B(n1 != n2)
          case (B(b1),B(b2)) => B(b1 != b2)
          case (S(s1),S(s2)) => B(s1 != s2)
          case (_,_) => B(toNumber(v1) != toNumber(v2))
        }

        case _ => throw new UnsupportedOperationException
      }
      case If(ifE, thenE, elseE) if isValue(ifE) => {
        if(toBoolean(ifE)) thenE
        else elseE
      }
      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2,v1,x)

      case Call(v1,v2) if isValue(v1) && isValue(v2) => v1 match {
        case Function(None, x, e1) => substitute(e1, v2, x)
        case Function(Some(x1), x2, e1) => substitute(substitute(e1, v1, x1), v2, x2)
        case _ => throw new DynamicTypeError(e)
      }

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
      case Unary(uop,e1) => Unary(uop,step(e1))
      case Binary(bop @ (Ne|Eq),Function(_,_,_),e2) => throw new DynamicTypeError(e)
      case Binary(bop,v1,e2) if isValue(v1) => Binary(bop,v1,step(e2))
      case Binary(bop,e1,e2) => Binary(bop,step(e1),e2)
      case If(ifE,thenE,elseE) => If(step(ifE),thenE,elseE)
      case ConstDecl(x,e1,e2) => ConstDecl(x,step(e1),e2)
      case Call(v1 @ Function(_,_,_),e2) => Call(v1,step(e2))
      case Call(v1,e2) if isValue(v1) => throw new DynamicTypeError(e)
      case Call(e1,e2) => Call(step(e1),e2)

        // ****** Your cases here

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }
  

  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  
  // Interface to run your big-step interpreter starting from an empty environment and print out
  // the test input if debugging.
  def evaluate(e: Expr): Expr = {
    require(closed(e))
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with eval ...")
      println("\nExpression:\n  " + e)
    }
    val v = eval(emp, e)
    if (debug) {
      println("Value: " + v)
    }
    v
  } 
  
  // Convenience to pass in a jsy expression as a string.
  def evaluate(s: String): Expr = evaluate(Parser.parse(s))
   
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  def iterateStep(e: Expr): Expr = {
    require(closed(e))
    def loop(e: Expr, n: Int): Expr = {
      if (debug) { println("Step %s: %s".format(n, e)) }
      if (isValue(e)) e else loop(step(e), n + 1)
    }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val v = loop(e, 0)
    if (debug) {
      println("Value: " + v)
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(Parser.parse(s))
  
  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val expr =
      handle(None: Option[Expr]) {Some{
        Parser.parseFile(file)
      }} getOrElse {
        return
      }
    
    handle() {
      val v1 = iterateStep(expr)
      println(pretty(v1))
    }
  }
    
}
