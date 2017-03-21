package jsy.student

object Lab4 extends jsy.util.JsyApplication {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * <Cameron Taylor>
   * 
   * Partner: <Jake Traut>
   * Collaborators: <Steven Conflenti, Jennifer Michael>
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
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */

  //remove adjacent duplicates left to right
  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => l
    case h1 :: (t1 @ (h2 :: _)) => {
      //remove adjacent elements if same
      if(h1 == h2) compressRec(t1)
        else h1 :: compressRec(t1)
    }
  }

  //right to left compressRec
  //acc is accumulator, starts empty and fills up
  //h1 is element in acc, check if same as last element in list (h)
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => acc match{
      case Nil => h :: acc
      case h1 :: _ => if(h == h1) acc
        else h :: acc
    }
  }

  //recursively finds first element in l that returns Some(x) when it is used as a parameter in f
  def mapFirst[A](f: A => Option[A])(l: List[A]): List[A] = l match {
    case Nil => l
    case h :: t => f(h) match {
      case None => h :: mapFirst(f)(t)
      case Some(x) => x :: t
    }
  }
  
  /* Search Trees */
  
  sealed abstract class Tree {
    def insert(n: Int): Tree = this match {
      case Empty => Node(Empty, n, Empty)
      case Node(l, d, r) => if (n < d) Node(l insert n, d, r) else Node(l, d, r insert n)
    } 

    //if node, recurse on left, apply function to data, recurse on right with the data
    def foldLeft[A](z: A)(f: (A, Int) => A): A = {
      def loop(acc: A, t: Tree): A = t match {
        case Empty => acc
        case Node(l, d, r) => loop(f(loop(acc, l), d), r)
      }
      loop(z, this)

    }
    
    def pretty: String = {
      def p(acc: String, t: Tree, indent: Int): String = t match {
        case Empty => acc
        case Node(l, d, r) =>
          val spacer = " " * indent
          p("%s%d%n".format(spacer, d) + p(acc, l, indent + 2), r, indent + 2)
      } 
      p("", this, 0)
    }
  }
  case object Empty extends Tree
  case class Node(l: Tree, d: Int, r: Tree) extends Tree
  
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }
  
  def sum(t: Tree): Int = t.foldLeft(0){ (acc, d) => acc + d }
  
  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = t.foldLeft((true, None: Option[Int])){
      (acc, d) => acc match {
        case (y, None) => (y, Some(d))
        case (y, Some(x)) => if (x < d && y) (y, Some(d)) else (false, Some(d))
      }
    }
    b
  }
  

  /* Type Inference */

  type TEnv = Map[String, Typ]
  val emp: TEnv = Map()
  def get(env: TEnv, x: String): Typ = env(x)
  def extend(env: TEnv, x: String, t: Typ): TEnv = env + (x -> t)
  
  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }
  
  def typeInfer(env: TEnv, e: Expr): Typ = {
    // Some shortcuts for convenience
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typ(e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => env(x)
      case ConstDecl(x, e1, e2) => typeInfer(extend(env, x, typ(e1)), e2)

      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case t => err(t, e1)
        //case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typ(e1) match {
        case TBool => TBool
        case t => err(t, e1)
      }

      case Binary(Plus, e1, e2) => (typ(e1), typ(e2)) match {
        case (TString, TString) => TString
        case (TNumber, TNumber) => TNumber

        case (TString, _) => err(typ(e2), e2)
        case (TNumber, _) => err(typ(e2), e2)

        case _ => err(typ(e1), e1)
      }
      case Binary(Minus|Times|Div, e1, e2) => (typ(e1), typ(e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TNumber, _) => err(typ(e2), e2)
        case _ => err(typ(e1), e1)
      }
      case Binary(Eq|Ne, e1, e2) => (typ(e1), typ(e2)) match {
        case (TNumber, TNumber) => TBool
        case (TNumber, _) => err(typ(e2), e2)
        case (TString, TString) => TBool
        case (TString, _) => err(typ(e2), e2)
        case (TBool, TBool) => TBool
        case (TBool, _) => err(typ(e2), e2)
        case (TObj(o1), TObj(o2)) => TBool
        case (TObj(o1), _) => err(typ(e2), e2)
        case (TUndefined, TUndefined) => TBool
        case (TUndefined, _) => err(typ(e2), e2)
        case (_, _) => err(typ(e1), e1)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typ(e1), typ(e2)) match {
        case (TString, TString) => TBool
        case (TNumber, TNumber) => TBool

        case (TString, _) => err(typ(e2), e2)
        case (TNumber, _) => err(typ(e2), e2)

        case (_, _) => err(typ(e1), e1)
      }
      case Binary(And|Or, e1, e2) => (typ(e1), typ(e2)) match {
        case (TBool, TBool) => TBool
        case (TBool, _) => err(typ(e2), e2)
        case (_, _) => err(typ(e1), e1)
      }
      case Binary(Seq, e1, e2) => {
        typ(e1);
        typ(e2)
      }
      case If(e1, e2, e3) => typ(e1) match {
        case TBool => if(typ(e2) == typ(e3)) typ(e2)
          else err(typ(e3), e3)
        case _ => err(typ(e2), e2)
      }
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(params, tret)
            extend(env, f, tprime)
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = env1 ++ params
        // Match on whether the return type is specified.
        tann match {
          case None => TFunction(params, typeInfer(env2, e1))
          case Some(x) => {
            if (x == typeInfer(env2, e1)) TFunction(params, x)
            else err(typeInfer(env2, e1), e1)
          }
        }
      }
      case Call(e1, args) => typ(e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params, args).zipped.foreach {
            (param, arg) => (param, arg) match {
              case((p, ptype), arg) => if(ptype != typ(arg)) err(typ(arg), arg)
            }
          };
          tret
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields.map{case (f, t) => (f, typ(t))})
      case GetField(e1, f) => typ(e1) match {
        case TObj(fields) => if (fields.contains(f)) fields(f)
          else err(typ(e1), e1)
        case _ => err(typ(e1), e1)
      }
    }
  }
  
  
  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case (N(n1), N(n2)) =>
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
      case _ => throw StuckError(Binary(bop, v1, v2))
    }
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v), "Expr to substitute is not a value")
    
    def subst(e: Expr): Expr = substitute(e, v, x)
    
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(subst(e1))
        /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if(y == x) v else Var(y)
      case ConstDecl(y, e1, e2) => if(y == x) ConstDecl(y, subst(e1), e2)
        else ConstDecl(y, subst(e1), subst(e2))
        /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) => {
        val exists = (params.exists((f:(String, Typ)) => f._1 == x) || p == Some(x))
        if(exists) e
          else Function(p, params, tann, subst(e1))
      }
      case Call(e1, args) => Call(subst(e1), args map subst)
        /***** New cases for Lab 4 */
      case Obj(fields) => Obj(fields.map(field => (field._1, subst(field._2))))
      case GetField(e1, f) => if (x != f) GetField(subst(e1), f)
        else e
    }
  }
  
  def step(e: Expr): Expr = {
    require(!isValue(e), "input Expr to step is a value")

    def stepIfNotValue(e: Expr): Option[Expr] = if (isValue(e)) None else Some(step(e))
    
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined

        /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
      case Unary(Neg, N(n1)) => N(- n1)
      case Unary(Not, B(b1)) => B(! b1)

      case Binary(Plus, N(n1), N(n2)) => N(n1 + n2)
      case Binary(Minus, N(n1), N(n2)) => N(n1 - n2)
      case Binary(Times, N(n1), N(n2)) => N(n1 * n2)
      case Binary(Div, N(n1), N(n2)) => N(n1 / n2)

      case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)

      case Binary(bop @(Lt|Gt|Le|Ge), v1, v2) if isValue(v1)&&isValue(v2) => B(inequalityVal(bop, v1, v2))
      case Binary(Eq, v1, v2) if isValue(v1)&&isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1, v2) if isValue(v1)&&isValue(v2) => B(v1 != v2)

      case Binary(And, B(b1), e2) => if(b1) e2 else B(b1)
      case Binary(Or, B(b1), e2) => if(b1) B(b1) else e2
      case Binary(Seq, v1, e2) if isValue(v1) => e2

      case If(B(b1), e2, e3) => if(b1) e2 else e3

      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x)

      case Call(v1, args) if isValue(v1) && (args forall isValue) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val e1p = (params, args).zipped.foldRight(e1) {
              case ((par, arg), body2) => substitute(body2, arg, par._1)
            }
            p match {
              case None => e1p
              case Some(x1) => substitute(e1p, v1, x1)
            }
          }
          case _ => throw StuckError(e)
        }

        /***** New cases for Lab 4. Make sure to replace the case _ => ???. */
      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))

        /***** Cases from Lab 3. Make sure to replace the case _ => ???. */
      case Unary(uop, e1) => Unary(uop, step(e1))

      case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, step(e2))
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)

      case If(e1, e2, e3) => If(step(e1), e2, e3)

      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)

        /***** Cases needing adapting from Lab 3 */
      case Call(v1 @ Function(_, _, _, _), args) if isValue(v1) => Call(v1, mapFirst(stepIfNotValue)(args))
      case Call(e1, args) => Call(step(e1), args)

        /***** New cases for Lab 4. Make sure to replace the case _ => ???. */

      case GetField(Obj(fields), f) => fields.get(f) match {
          case Some(x) =>x
          case None => throw StuckError(e)
      }
      case GetField(e1, f) => GetField(step(e1), f)

      case Obj(fields) => {
        val fieldList = fields.toList
        def stepToValue(field: (String, Expr)): Option[(String, Expr)] = {
          field match {
            case (s1, e2) => if(isValue(e2)) None else Some(s1, step(e2))
          }
        }
        val valueList = mapFirst(stepToValue)(fieldList)
        val fieldMap = valueList.toMap
        Obj(fieldMap)
      }

      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }
  
  
  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information

  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    } 
    val t = typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }
  
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  def iterateStep(e: Expr): Expr = {
    require(closed(e), "input Expr to interateStep is not closed")
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

  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val e1 =
      handle(None: Option[Expr]) {Some{
        Parser.parseFile(file)
      }} getOrElse {
        return
      }

    val welltyped = handle(false) {
      println("# Type checking ...")
      val t = Lab4.inferType(e1)
      println(pretty(t))
      true
    }
    if (!welltyped) return

    handle() {
      println("# Stepping ...")
      def loop(e: Expr, n: Int): Expr = {
        println("## %4d: %s".format(n, e))
        if (isValue(e)) e else loop(Lab4.step(e), n + 1)
      }
      val v1 = loop(e1, 0)
      println(pretty(v1))
    }
  }

}
