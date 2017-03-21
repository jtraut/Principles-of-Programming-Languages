package jsy.student

object Lab5 extends jsy.util.JsyApplication {
  import jsy.lab5.ast._
  import jsy.lab5._
  import jsy.lab5.DoWith._

  /*
   * CSCI 3155: Lab 5
   * Steven Conflenti
   *
   * Partner: Jake Traut, Brent Fosdick
   * Collaborators: Cameron Taylor, Jessica Petty, Jennifer Michael
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

  /*** Exercise with DoWith ***/

  def fresh: DoWith[Int,String] = doget flatMap { i =>
    val xp = "x" + i
    doput(i + 1) map { _ => xp }
  }

  def rename(env: Map[String, String], e: Expr): DoWith[Int,Expr] = {
    def ren(e: Expr): DoWith[Int,Expr] = rename(env, e)
    e match {
      case N(_) => doreturn(e)
      case Var(x) => doreturn(Var(env(x)))
      case Binary(Plus, e1, e2) => {
        ren(e1) flatMap {
          e1p => ren(e2) map {
            e2p => Binary(Plus, e1p, e2p)
          }
        }
      }
      case Decl(MConst, x, e1, e2) =>
        fresh flatMap {
          xp => ren(e1) flatMap {
            e1p => rename(env + (x->xp),e2) map {
              e2p => Decl(MConst, xp, e1p, e2p)
            }
          }
        }


      /* For this exercise, no need to implement any more cases than the ones above.
       * Leave the following default case. */
      case _ => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }

  def rename(e: Expr): Expr = {
    val (_, r) = rename(Map.empty, e)(0)
    r
  }

  def rename(s: String): Expr = rename(Parser.parse(s))

  /*** Helper: mapFirst to DoWith ***/

  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
  def mapFirstWith[W,A](f: A => Option[DoWith[W,A]])(l: List[A]): DoWith[W,List[A]] = l match {
    case Nil => doreturn(l)
    case h :: t => f(h) match {
      //recurse on the rest of the list, mapping the list to another list with the prepended on the modified all
      //case None => mapFirstWith(f)(t).map((t2: List[A]) => (h :: t2))
      case None => mapFirstWith(f)(t) map {tp => h :: tp}
      //map the modified element to the tail
      case Some(x) => x map {hp => hp :: t}
      //x = hpinabox
      //case Some(x) => x.map((element: A) => (element :: t))
    }
  }

  /*** Casting ***/
  
  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
    case (TNull, TObj(_)) => true
    case (_,_) if (t1 == t2) => true
    case (TObj(fields1),TObj(fields2)) => {
      val check1 = fields1.forall {
        case (field_1, t_1) => fields1.get(field_1) match {
          case Some(t_2) => if(t_1 == t_2) true else false
          case None => true
        }
      }
      val check2 = fields2.forall {
        case (field_1, t_1) => fields2.get(field_1) match {
          case Some(t_2) => if(t_1 == t_2) true else false
          case None => true
        }
      }
      check1 || check2
    }


    /*fields1.forall{
      case(name,typ) if (typ == None) => true
      case(name,typ1) => fields2.get(name) match {
        case None => true
        case Some(typ2) => castOk(typ1,typ2)
      }
    }*/
    /***** Cases for the extra credit. Do not attempt until the rest of the assignment is complete. */
    case (TInterface(tvar, t1p), _) => ???
    case (_, TInterface(tvar, t2p)) => ???
      /***** Otherwise, false. */
    case _ => false
  }
  
  /*** Type Inference ***/

  type TEnv = Map[String, (Mutability,Typ)]
  val emp: TEnv = Map()
  def get(env: TEnv, x: String): (Mutability,Typ) = env(x)
  def extend(env: TEnv, x: String, mt: (Mutability,Typ)): TEnv = env + (x -> mt)

  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  } 

  // A helper function to translate parameter passing mode to the mutability of
  // the variable.
  def mut(m: PMode): Mutability = m match {
    case PName => MConst
    case PVar | PRef => MVar
  }

  def typeInfer(env: TEnv, e: Expr): Typ = {
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typ(e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) =>
        val (_, t) = env(x)
        t

        /***** Cases directly from Lab 4. We will minimize the test of these cases in Lab 5. */
      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typ(e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => (typ(e1), typ(e2)) match {
        case (TString, TString) => TString
        case (TNumber, TNumber) => TNumber
        case (TNumber, tgot) => err(tgot, e2)
        case (TString, tgot) => err(tgot, e2)
        case (_, _) => err(typ(e1), e1)
      }
      case Binary(Minus|Times|Div, e1, e2) => (typ(e1), typ(e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TNumber, tgot) => err(tgot, e1)
        case (tgot, _) => err(tgot, e1)
      }
      case Binary(Eq|Ne, e1, e2) => (typ(e1), typ(e2)) match {
        case (TFunction(_, _), _) => err(typ(e1), e1)
        case (tgot1, tgot2) => if (tgot1 == tgot2) TBool else err(typ(e2), e2)
        case (_, _) => err(typ(e1), e1)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typ(e1), typ(e2)) match {
        case (TNumber, TNumber) => TBool
        case (TString, TString) => TBool
        case (TNumber, tgot) => err(tgot, e2)
        case (TString, tgot) => err(tgot, e2)
        case (_, _) => err(typ(e1), e1)
      }
      case Binary(And|Or, e1, e2) => (typ(e1), typ(e2)) match {
        case (TBool, TBool) => TBool
        case (TBool, tgot) => err(tgot, e2)
        case (_, _) => err(typ(e1), e1)
      }
      case Binary(Seq, e1, e2) =>
        typ(e1); typ(e2)

      case If(e1, e2, e3) => {
        if(typ(e1) != TBool) return err(typ(e1), e1)
        if(typ(e2) == typ(e3)) typ(e2) else err(typ(e3), e3)
      }
      case Obj(fields) => TObj(fields.map{case (obj, e) => (obj, typ(e))})

      case GetField(e1, f) => typ(e1) match {
        case TObj(field) => if (field.contains(f)) field(f) else err(typ(e1), e1)
        case _ => err(typ(e1), e1)
      }

        /***** Cases from Lab 4 that need a small amount of adapting. */
      case Decl(mut, x, e1, e2) =>
        //create a new environment, addding mappings from x to the (mut,type) tuple
        val env2 = env + (x -> (mut,typ(e1)))
        //infer the type of the modified environment
        typeInfer(env2,e2)
        //e2 is mapped to the type of mut x

      //TypeFunction, TypeRecFunction, TypeFunctionAnn
      case Function(p, paramse, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {


          case (Some(f), Some(tret)) =>
            val tprime = TFunction(paramse, tret)
            env + (f -> (MConst, tprime))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }

        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = paramse match{
          case Left(params) => {
            params.foldLeft(env1) { case (acc, (k, v)) => acc + (k -> (MConst, v))}
          }

          case Right((mutability, x,t)) => mutability match{
            case PName => env1 + (x -> (MConst, t)) //if passed by name, map to const mut type and type
            case _ => env1 + (x -> (MVar, t)) //if its not const, pass as variable
          }
        }
        // Match on whether the return type is specified.
        val t1 = typeInfer(env2, e1)
        tann foreach { rt => if (rt != t1) err(t1, e1)};
        TFunction(paramse, t1)
      }

      case Call(e1, args) => typ(e1) match {

        //TypeCall(list of params)
        case TFunction(Left(params), tret) if (params.length == args.length) => {
          (params, args).zipped.foreach {
            case ((_, tparam), argExp) => if (tparam != typ(argExp)) err(typ(argExp), argExp)
          }
          tret
        }
        //TypeCall (function with mode and params)
        case tgot @ TFunction(Right((mode,_,tparam)), tret) => mode match{

          //TypeCallRef (given a location)
          case PRef => {
            val h::_ = args
            if(tparam == typeInfer(env, h) && isLExpr(h)) tret
            else err(typeInfer(env, h), h)
          }
          //TypeCallNameVar
          case _ => {
            val h::_ = args
            if(tparam != typeInfer(env, h)) err(typeInfer(env, h), h)
            else tret
          }
        }
        case tgot => err(tgot, e1)
      }

      /***** New cases for Lab 5. ***/
      //TypeAssignVar
      case Assign(Var(x), e1) =>
        env.get(x) match{
          case Some((MVar, typ2)) if (typ(e1) == typ2) => typ2
          case _ => err(typ(e1), e1)
        }

      //TypeAssignField
      case Assign(GetField(e1, f), e2) => typ(e1) match {
        case TObj(tfields) if (tfields.contains(f)) => {
          if (tfields(f) == typ(e2)) {
            typ(e2)
          }
          else {
            err(typ(e2), e2)
          }
        }
      }
      case Assign(_, _) => err(TUndefined, e)

      //TypeNull
      case Null => TNull

      //TypeCast
      case Unary(Cast(t), e1) => typ(e1) match {
        case tgot if (castOk(tgot, t)) => t
        case tgot => err(tgot, e1)
      }

      /* Should not match: non-source expressions or should have been removed */
      case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }
  
  /*** Small-Step Interpreter ***/

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3 and Lab 4.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), "v1 in inequalityVal is not a value")
    require(isValue(v2), "v2 in inqualityVal is not a value")
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
  
  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    /* We removed the requirement that esub is a value to support call-by-name. */
    //require(isValue(esub), "Expr to substitute is not a value")
    /* We suggest that you add support for call-by-name last. */
    def subst(e: Expr): Expr = substitute(e, esub, x)
    val ep: Expr = avoidCapture(freeVars(esub),e)
    ep match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
      case Print(e1) => Print(subst(e1))
        /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) esub else e
        /***** Cases need a small adaption from Lab 3 */
      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x == y) e2 else subst(e2))
        /***** Cases needing adapting from Lab 4 */
      case Function(p, paramse, retty, e1) => paramse match {
        case Left(params) =>
          if (params.foldLeft(false)((bool,param) => (param._1 == x) || bool) ||  Some(x) == p) e
          else Function(p,paramse,retty,subst(e1))
        case Right((_,name,typ)) =>
          if (name == x || p == Some(x)) e else Function(p,paramse,retty,subst(e1))
      }
        /***** Cases directly from Lab 4 */
      //calls substitute on e1 and each argument
      case Call(e1, args) => Call(subst(e1), args map subst)
      case Obj(fields) => Obj(fields.map(field => (field._1, subst(field._2))))
      case GetField(e1, f) => if (x != f) GetField(subst(e1), f) else e
        /***** New case for Lab 5 */
      case Assign(e1, e2) => Assign(subst(e1),subst(e2))
        /***** Extra credit case for Lab 5 */
      case InterfaceDecl(tvar, t, e1) => InterfaceDecl(tvar, t, subst(e1))
    }
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))
    
    /*** Helpers for Call ***/
    
    def stepIfNotValue(e: Expr): Option[DoWith[Mem,Expr]] = if (isValue(e)) None else Some(step(e))
    
    /* Check whether or not the argument expression is ready to be applied. */
    def argApplyable(mode: PMode, arg: Expr): Boolean = mode match {
      case PVar => isValue(arg)
      case PName => true
      case PRef => isLValue(arg)
    }

    /*** Body ***/
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => doget map { m => println(pretty(m, v1)); Undefined }
        /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
      case Unary(Neg, N(n1)) => doreturn(N(-n1))
      case Unary(Not, B(b1)) => doreturn(B(!b1))
      case Binary(Plus, N(n1), N(n2)) => doreturn(N(n1 + n2))
      case Binary(Plus, S(s1), S(s2)) => doreturn(S(s1 + s2))
      case Binary(Minus, N(n1), N(n2)) => doreturn(N(n1 - n2))
      case Binary(Times, N(n1), N(n2)) => doreturn(N(n1 * n2))
      case Binary(Div, N(n1), N(n2)) => doreturn(N(n1 / n2))
      case Binary(bop @ (Lt|Gt|Le|Ge), v1, v2) if (isValue(v1) && isValue(v2)) =>
        doreturn(B(inequalityVal(bop, v1, v2)))
      case Binary(Eq, v1, v2) if (isValue(v1) && isValue(v2)) =>
        doreturn(B(v1 == v2))
      case Binary(Ne, v1, v2) if (isValue(v1) && isValue(v2)) =>
        doreturn(B(v1 != v2))
      case Binary(And, B(b1), e2) => doreturn(if (b1) e2 else B(b1))
      case Binary(Or, B(b1), e2) => doreturn(if (b1) B(b1) else e2)
      case Binary(Seq, v1, e2) if (isValue(v1)) => doreturn(e2)
      case If(B(b1), e2, e3) => doreturn(if (b1) e2 else e3)

        /***** Cases needing adapting from Lab 4. Make sure to replace the case _ => ???. */
      case Obj(fields) if (fields forall { case (_, vi) => isValue(vi)}) => memalloc(e)
        //the value of an object is an address
        //doget...
        //get address
        //doput
        //map final result to an addr
        //refer to ast memalloc function -> generates a fresh address
      case GetField(a @ A(_), f) => doget map {mem => mem(a) match {
        case Obj(fields) => fields(f)
        case _ => throw StuckError(e)
      }}

      case Call(v1, args) if isValue(v1) =>
        def substfun(e1: Expr, p: Option[String]): Expr = p match {
          case None => e1
          case Some(x) => substitute(e1, v1, x)
        }
        (v1, args) match {
          /*** Fill-in the DoCall cases, the SearchCall2, the SearchCallVar, the SearchCallRef  ***/
          // DoCall / DoCallRec
          case (Function(p,Left(params),tann,e1),args) if (args forall isValue) =>
            if (params.length != args.length) throw StuckError(e);
            val e1p = (params,args).zipped.foldRight(e1) { case (((p,_),a),acc) => substitute(acc,a,p) }
            doreturn(substfun(e1p, p))

          // DoCallName / DoCallRecName
          case (Function(p,Right((PName,x1,typ)),tann,e1),e2 :: Nil) =>
            doreturn(substfun(substitute(e1,e2,x1),p))

          // DoCallVar / DoCallRecVar
          case (Function(p, Right((PVar, x1, _)), _, e1), v2::Nil) if (isValue(v2)) => {
            memalloc(v2) map {
              a => substfun(substitute(e1, Unary(Deref, a), x1), p)
            }
          }

          // DoCallRef / DoCallRecRef
          case (Function(p,Right((PRef,x1,typ)),tann,e1),lv2 :: Nil) if isLValue(lv2) =>
            doreturn(substfun(substitute(e1,lv2,x1),p))

          // SearchCall2
          case (Function(_,Left(_),_,_),args) =>
            for (argsp <- mapFirstWith(stepIfNotValue)(args)) yield Call(v1,argsp)

          // SearchCallVar
          case (Function(_,Right((PVar,_,_)),_,_),e2 :: Nil) =>
            for (e2p <- step(e2)) yield Call(v1,List(e2p))

          // SearchCallRef
          case (Function(_,Right((PRef,_,_)),_,_),e2 :: Nil) if (!isLValue(e2)) =>
            for (e2p <- step(e2)) yield Call(v1,List(e2p))

          case _ => throw StuckError(e)
        }

      case Decl(MConst, x, v1, e2) if isValue(v1) =>
        doreturn(substitute(e2, v1, x))
      case Decl(MVar, x, v1, e2) if isValue(v1) =>
        //memalloc returns doWith with address
        memalloc(v1) map { a => substitute(e2, Unary(Deref, a), x)}

        /***** New cases for Lab 5. */
      case Unary(Deref, a @ A(_)) =>
        doget map {m => m(a)}

      // DoAssignVar
      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        domodify[Mem] { (m:Mem) => m + (a -> v) } map { _ => v}

      // DoAssignField
      case Assign(GetField(a @ A(_),f), vp) if isValue(vp) =>
        domodify[Mem] { (m:Mem) =>
          //at A we must have Obj(fields)
          //fields must contain f
          val fields = m.get(a) match {
            case Some(Obj(fields)) if (fields.contains(f)) => fields
            case _ => throw new StuckError(e)
          }
          m + (a -> Obj(fields + (f -> vp)))
        } map { _ => vp }

    /* Base Cases: Error Rules */
      /*** Fill-in cases here. ***/
      case Unary(Cast(t),e1) => e1 match {
        // DoCastNull
        case Null => doreturn(Null)
        // DoCastObj / TypeErrorCastObj
        case a @ A(_) => doget map { m =>
          val tfields : Map[String,Typ] = (t: @unchecked) match {
            case TObj(tfields) => tfields
            case TInterface(_,TObj(tfields)) => tfields
          }
          m.get(a) match {
            case Some(Obj(fields)) =>
              if (tfields.forall((t) => fields.contains(t._1))) a
              else throw new DynamicTypeError(e)
            case _ => throw new StuckError(e)
          }
        }

        // DoCast
        case v if isValue(v) => v match {
          case Null | A(_) => throw new StuckError(e)
          case _ => doreturn(v)
        }
        case _ => throw new StuckError(e)
      }

      // NullErrorGetField / NullErrorAssignField
      case GetField(Null,_) | Assign(GetField(Null,_),_) => throw new NullDereferenceError(e)

      /* Inductive Cases: Search Rules */
      case Print(e1) =>
        for (e1p <- step(e1)) yield Print(e1p)
      case Unary(uop, e1) =>
        for (e1p <- step(e1)) yield Unary(uop, e1p)
      case Binary(bop, v1, e2) if isValue(v1) =>
        for (e2p <- step(e2)) yield Binary(bop, v1, e2p)
      case Binary(bop, e1, e2) =>
        for (e1p <- step(e1)) yield Binary(bop, e1p, e2)
      case If(e1, e2, e3) =>
        for (e1p <- step(e1)) yield If(e1p, e2, e3)
      case Obj(fields) => fields find { case (_, ei) => !isValue(ei) } match {
        case Some((fi,ei)) =>
          for (eip <- step(ei)) yield Obj(fields + (fi -> eip))
        case None => throw StuckError(e)
      }
      // SearchGetField
      case GetField(e1, f) =>
        for (e1p <- step(e1)) yield GetField(e1p, f)

      /*** Fill-in more Search cases here. ***/
      case Decl(mod, x, e1, e2) =>
        for (e1p <- step(e1)) yield Decl(mod, x, e1p, e2)
      // SearchCall1
      case Call(e1,args) =>
        for (e1p <- step(e1)) yield Call(e1p, args)
      // SearchAssign1
      case Assign(e1,e2) if !isLValue(e1) =>
        for (e1p <- step(e1)) yield Assign(e1p,e2)
      // SearchAssign2
      case Assign(lv1,e2) =>
        for (e2p <- step(e2)) yield Assign(lv1,e2p)


      /* Everything else is a stuck error. */
      case _ =>
        println("error on: " + e)
        throw StuckError(e)
    }
  }

  /*** Extra Credit: Lowering: Remove Interface Declarations ***/

  def removeInterfaceDecl(e: Expr): Expr =
    /* Do nothing by default. Change to attempt extra credit. */
    e

  /*** External Interfaces ***/

  //this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.
  
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
  
  case class TerminationError(e: Expr) extends Exception {
    override def toString = Parser.formatErrorMessage(e.pos, "TerminationError", "run out of steps in evaluating " + e)
  }
  
  def iterateStep(e: Expr): Expr = {
    require(closed(e), "input Expr to iterateStep is not closed: free variables: %s".format(freeVars(e)) )
    def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
      if (Some(n) == maxSteps) throw TerminationError(e)
      else if (isValue(e)) doreturn( e )
      else {
        for {
          m <- doget[Mem]
          _ = if (debug) { println("Step %s:%n  %s%n  %s".format(n, m, e)) }
          ep <- step(e)
          epp <- loop(ep, n + 1)
        } yield
        epp
      }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val (m,v) = loop(e, 0)(memempty)
    if (debug) {
      println("Result:%n  %s%n  %s".format(m,v))
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(removeInterfaceDecl(jsy.lab5.Parser.parse(s)))

  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val expr =
      handle(None: Option[Expr]) {Some{
        jsy.lab5.Parser.parseFile(file)
      }} getOrElse {
        return
      }
      
    val exprlowered =
      handle(None: Option[Expr]) {Some{
        removeInterfaceDecl(expr)
      }} getOrElse {
        return
      }

    val welltyped = handle(false) {
      println("# Type checking ...")
      val t = inferType(exprlowered)
      println("## " + pretty(t))
      true
    }
    if (!welltyped) return

    handle() {
      println("# Stepping ...")
      def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
        if (Some(n) == maxSteps) throw TerminationError(e)
        else if (isValue(e)) doreturn( e )
        else {
          for {
            m <- doget[Mem]
            _ = println("## %4d:%n##  %s%n##  %s".format(n, m, e))
            ep <- step(e)
            epp <- loop(ep, n + 1)
          } yield
          epp
        }
      val (m,v) = loop(exprlowered, 0)(memempty)
      println("## %s%n%s".format(m,pretty(v)))
    }
  }
    
}
