package jsy.student

object Lab5 extends jsy.util.JsyApplication {
  import jsy.lab5.ast._
  import jsy.lab5._
  import jsy.lab5.DoWith._

  /*
   * CSCI 3155: Lab 5
   * <Steven Carpenter>
   *
   * Partner: <Landon>
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
      case N(n) => doget flatMap {i => doput(i) map {_ => e}}
      case Binary(Plus, e1, e2) => ren(e1) flatMap {e1p => ren(e2)  map {e2p =>Binary(Plus, e1p, e2p)}}
      case Var(x) => doget flatMap  { i => doput(i) map { _ => Var(env(x))}}
      case Decl(MConst, x, e1, e2) =>
        fresh flatMap { xp =>
          ren(e1) flatMap{elp =>
            val envp = env + (x->xp)
            rename(envp,e2) map {e2p =>
              Decl(MConst, xp, elp, e2p)
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
    case Nil => doreturn(Nil)
    case h :: t => f(h) match {
      case None => mapFirstWith(f)(t) map{tp => h :: tp}
      case Some(hpinbox) => hpinbox map{hp => hp :: t}
    }
  }

  /*** Casting ***/
  
  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
      /***** Make sure to replace the case _ => ???. */
    case (TNull, TObj(_)) => true
    case (_,_) if (t1==t2) => true
    case (TObj(f1),TObj(f2)) =>
      val (sm,lg) = if (f1.size < f2.size) (f1,f2) else (f2,f1)
      sm.forall(lg.toList.contains)
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
      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
        /***** Cases directly from Lab 4. We will minimize the test of these cases in Lab 5. */
      case Unary(Not, e1) => typ(e1) match {
        case TBool => TBool
        case tgot => err(tgot,e1)
      }
      case Binary(Plus, e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match{
          case TNumber => TNumber
          case tgot => err(typ(e2),e2)
        }
        case TString => typ(e2) match{
          case TString => TString
          case tgot => err(typ(e2),e2)
        }
        case tgot => err(typ(e1),e1)

      }
      case Binary(Minus|Times|Div, e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match{
          case TNumber => TNumber
          case tgot => err(typ(e2),e2)
        }

        case tgot => err(typ(e1),e1)
      }
      case Binary(Eq|Ne, e1, e2) => (typ(e1),typ(e2)) match {
        case (TFunction(param,tret),_) => err(TFunction(param,tret),e1)
        case (_,TFunction(param,tret)) => err(TFunction(param,tret),e1)
        case (t1,t2) => if(t1 == t2) TBool else err(t2,e2)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => typ(e1) match {
        case TNumber => typ(e2) match{
          case TNumber => TBool
          case tgot => err(tgot,e2)
        }
        case TString => typ(e2) match{
          case TString => TBool
          case tgot => err(tgot,e2)
        }
        case tgot => err(tgot,e1)
      }
      case Binary(And|Or, e1, e2) => (typ(e1),typ(e2)) match {
        case (TBool,TBool) => TBool
        case (TBool,tgot) => err(tgot,e2)
        case (tgot,_) => err(tgot,e1)
      }
      case Binary(Seq, e1, e2) => typ(e1);typ(e2)
      case If(e1, e2, e3) =>
        val tgot = typ(e1)
        if(tgot == TBool){
          val tgot2 = typ(e2)
          val tgot3 = typ(e3)
          if(tgot2 == tgot3){
            tgot2
          }
          else{err(tgot3,e3)
          }
        }
        else{err(tgot,e1)
        }
      case Obj(fields) => TObj(fields.map { case (t,e1) => (t, typ(e1))})
      case GetField(e1, f) => typ(e1) match {
        case TObj(tfields) if (tfields.contains(f)) => tfields(f)
        case tgot => err(tgot,e1)
      }

        /***** Cases from Lab 4 that need a small amount of adapting. */
      case Decl(mut, x, e1, e2) => typeInfer(env + (x -> (mut, typ(e1))), e2)
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(params, tret)
            env + (f -> (MConst,tprime))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params match{
          case Left(params) => params.foldLeft(env1) {
            case (env,param) => param match {
              case (a,b) => env + (a -> (MConst, b))
            }
          }
          case Right((mode, x, t)) => mode match {
            case PName => env1 + (x -> (MConst, t))
            case _ => env1 + (x -> (MVar, t))
          }
        }

        val t1 = typeInfer(env2,e1)
        // Match on whether the return type is specified.
        tann foreach {
          rt => if(rt != t1) err(t1,e1)
        }
        TFunction(params,t1)
      }
      case Call(e1, args) => typ(e1) match {
        case TFunction(Left(params), tret) if (params.length == args.length) =>
          (params, args).zipped.foreach {
            case ((_, t), x) => if (t != typ(x)) err(t, x)
          };
          tret
        case tgot @ TFunction(Right((mode,_,tparam)), tret) =>
          val targ0 = typ(args(0))
          mode match {
            case PName | PVar => {
              if (targ0 != tparam) {
                err(targ0, args(0))
              } else {
                tret
              }
            }
            case PRef if isLExpr(args(0)) => {
              if (targ0 != tparam) {
                err(targ0, args(0))
              } else {
                tret
              }
            }
            case _ => err(tparam, args(0))
          }
        case tgot => err(tgot, e1)
      }

        /***** New cases for Lab 5. ***/
      case Assign(Var(x), e1) =>  env.get(x) match {
        case Some((mu,t)) if ((mu == MVar) && (t == typ(e1))) => t
        case _ => err(typ(e1),e1)
      }
      case Assign(GetField(e1, f), e2) => typ(e1) match {
        case TObj(tfields) if (tfields.contains(f) && tfields(f) == typ(e2)) => tfields(f)
        case tgot => err(tgot,e1)
      }
      case Assign(_, _) => err(TUndefined, e)

      case Null => TNull

      case Unary(Cast(t), e1) => typ(e1) match {
        case tgot if castOk(tgot,t) => t
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
    ((v1, v2): @unchecked) match {
      case (S(x),S(y)) => (bop: @unchecked) match{
        case Lt =>  x < y
        case Le =>  x <= y
        case Gt =>  x > y
        case Ge => x >= y
      }
      case (N(x),N(y)) => (bop: @unchecked) match{
        case Lt =>  x < y
        case Le =>  x <= y
        case Gt =>  x > y
        case Ge => x >= y
      }
    }
  }
  
  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    /* We removed the requirement that esub is a value to support call-by-name. */
    //require(isValue(esub), "Expr to substitute is not a value")
    /* We suggest that you add support for call-by-name last. */
    def subst(e: Expr): Expr = substitute(e, esub, x)
    val ep: Expr = avoidCapture(freeVars(esub), e)
    ep match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
      case Print(e1) => Print(subst(e1))
        /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop,subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1),subst(e2),subst(e3))
      case Var(y) => if(y == x) esub else e
        /***** Cases need a small adaption from Lab 3 */
      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x == y) e2 else subst(e2))
        /***** Cases needing adapting from Lab 4 */
      case Function(p, paramse, retty, e1) => paramse match {
        case Left(params) => {
          val e1p = params.foldLeft(e1) {
            (e1, param) => param match {
              case (pname, ptype) => if (pname != x && p != Some(x)) {
                subst(e1)
              }
                else e1
            }
          }
          Function(p, Left(params), retty, e1p)
        }
        case Right((pmode, pname, ptype)) => {
          val e1p = {
            if (pname != x && p != Some(x)) {
              subst(e1)
            } else e1
          }
          Function(p, Right(pmode, pname, ptype), retty, e1p)
        }
      }
        /***** Cases directly from Lab 4 */
      case Call(e1, args) => Call(subst(e1),args map subst)
      case Obj(fields) => Obj(fields.map{case (f,e1) => (f,subst(e1))})
      case GetField(e1, f) => GetField(subst(e1),f)
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
    def isObj(t: Typ): Boolean = t match {
      case TObj(_) | TInterface(_,TObj(_)) => true
      case _ => false
    }
    def isNull(t: Typ): Boolean = t match {
      case TNull => true
      case _ => false
    }

    /*** Body ***/
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => doget map { m => println(pretty(m, v1)); Undefined }
        /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
      case Unary(Neg, v1) if isValue(v1) => v1 match{
        case N(n) => doreturn(N(-n))
        case _ => throw StuckError(e)
      }
      case Unary(Not, v1) if isValue(v1) => v1 match{
        case B(n) => doreturn(B(!n))
        case _ => throw StuckError(e)
      }
      case Binary(Seq,v1,v2) if( isValue(v1) ) => doreturn(v2)
      case Binary(And,B(x),v2) => if (x) doreturn(v2) else doreturn(B(false))
      case Binary(Or,B(x),v2) => if (x) doreturn(B(true)) else doreturn(v2)
      case Binary(bop @ (Lt|Le|Gt|Ge),v1,v2) if(isValue(v1) && isValue(v2)) => doreturn(B(inequalityVal(bop,v1,v2)))
      case Binary(Eq,v1,v2) if(isValue(v1) && isValue(v2)) => doreturn(B(v1 == v2))
      case Binary(Ne,v1,v2) if(isValue(v1) && isValue(v2)) => doreturn(B(v1 != v2))
      case Binary(Plus,S(x),S(y)) => doreturn(S(x + y))
      case Binary(Plus,N(x),N(y)) => doreturn(N(x + y))
      case Binary(Minus,N(x),N(y)) => doreturn(N(x - y))
      case Binary(Times,N(x),N(y)) => doreturn(N(x * y))
      case Binary(Div,N(x),N(y)) => doreturn(N(x / y))

      case If(B(true),v2,v3)  => doreturn(v2)
      case If(B(false),v2,v3)  => doreturn(v3)
      //case _ => ???
        /***** Cases needing adapting from Lab 4. Make sure to replace the case _ => ???. */
      case Obj(fields) if (fields forall { case (_, vi) => isValue(vi)}) =>
        // doget the mem
        // update the mem
        // doput the mem
        // map _ => a}
        memalloc(e)

      case GetField(a @ A(_), f) =>
        doget map { m => m.get(a) match {
          case Some(Obj(fields)) => fields.get(f) match{
            case Some(field) => field
            case _ => throw StuckError(e)
          }
          case _ => throw StuckError(e)
        }
        }

      case Call(v1, args) if isValue(v1) =>
        def substfun(e1: Expr, p: Option[String]): Expr = p match {
          case None => e1
          case Some(x) => substitute(e1, v1, x)
        }
        (v1, args) match {
          case (Function(p,Left(paramse),_,e1),args) => {
            if (args forall isValue) {
              val e1p = (paramse.map { case (str, tp) => str }, args).zipped.foldRight(e1) {
                case ((str, ex), acc) => substitute(acc, ex, str)
                //substitute args
              }
              doreturn(substfun(e1p, p))
            }else{
              mapFirstWith(stepIfNotValue)(args) map {args => Call(v1,args)}
            }
          }
          case (Function(p,Right((PName, pname, ptype)),_,e1),List(e2)) =>
            doreturn(substfun(substitute(e1,e2,pname),p))

          case (Function(p,Right((PVar, pname, ptype)),_,e1),List(v2)) =>
            if(isValue(v2)) {
              memalloc(v2) map { a => substfun(substitute(e1, Unary(Deref, a), pname), p) }
            }else{
              step(v2) map { v2p => Call(v1,List(v2p))}
            }

          case (Function(p,Right((PRef, pname, ptype)),_,e1),List(lv2)) if (isLValue(lv2)) =>
              doreturn(substfun(substitute(e1, lv2, pname), p))
          case (Function(p,Right((PRef, pname, ptype)),_,e1),List(lv2)) if (!isLValue(lv2)) =>
              step(lv2) map { v2p => Call(v1,List(v2p))}

          /*** Fill-in the DoCall cases, the SearchCall2, the SearchCallVar, the SearchCallRef  ***/
          case _ => throw StuckError(e)
        } 
      
      case Decl(MConst, x, v1, e2) if isValue(v1) => doreturn(substitute(e2,v1,x))
      case Decl(MVar, x, v1, e2) if isValue(v1) => memalloc(v1) flatMap { a => doreturn(substitute(e2,Unary(Deref,a),x))}

        /***** New cases for Lab 5. */
      case Unary(Deref, a @ A(_)) => doget[Mem] flatMap { m => doreturn(m(a))}

      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        domodify[Mem] { m => if(m.contains(a)){
          m + (a->v)
        } else {
          throw new StuckError(e)
        }} flatMap { _ => doreturn(v) }

      case Assign(GetField(a @ A(_), f), v) if isValue(v) =>
        domodify[Mem] { m => m.get(a) match {
          case Some(Obj(fields)) if (fields.contains(f)) => m + (a -> Obj(fields + (f -> v)))
          case _ => throw new StuckError(e)
        }} flatMap  { _ => doreturn(v)}

      /* Base Cases: Error Rules */
        /***** Replace the following case with a case to throw NullDeferenceError.  */
      case Unary(Cast(t),e1) if isValue(e1)=> e1 match {
        case Null if isObj(t) => doreturn(Null)

        case a @ A(_) if isObj(t) => doget map { m =>
          val ftype: Map[String,Typ] = (t: @unchecked) match {
            case TObj(ftype) => ftype
            case TInterface(_,TObj(ftype)) => ftype
          }
          m.get(a) match {
            case Some(Obj(f)) =>
              if(ftype.forall((t) => f.contains(t._1))) a
              else throw new DynamicTypeError(e)
            case _ => throw new StuckError(e)
          }
        }
        case v1 if isValue(v1) => v1 match {
          case Null | A(_) => throw new StuckError(e)
          case _ => doreturn(v1)
        }
        case _ => throw new StuckError(e)
      }
      case Unary(Cast(t),e1) => step(e1) map{ e1p => Unary(Cast(t),e1p)}

      case GetField(Null,_) => throw NullDereferenceError(e)
      case Assign(GetField(Null,_),_) => throw NullDereferenceError(e)

      /* Inductive Cases: Search Rules */
        /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
      case Print(e1) => step(e1) map { e1p => Print(e1p) }
      case Unary(uop, e1) =>  step(e1) map {e1p => Unary(uop, e1p)}
      case Binary(bop,e1,e2) if isValue(e1) => step(e2) map {e1p => Binary(bop,e1,e1p)}
      case Binary(bop,e1,e2) => step(e1) map {e1p => Binary(bop,e1p,e2)}
      case If(e1,e2,e3) => step(e1) map {e1p => If(e1p,e2,e3)}
      //case _ => ???
      case Call(e1, args) => step(e1) map { e1p => Call(e1p, args)}
      case Decl(mut, x, e1, e2) => step(e1) map { e1p => Decl(mut, x, e1p, e2)}
        /***** Cases needing adapting from Lab 4 */
      case GetField(e1, f) => step(e1) map {e1p => GetField(e1p, f)}
      case Obj(fields) => fields find { case (_,ei) => !isValue(ei)} match{
        case Some((fi,ei)) =>
          step(ei) map {eip => Obj(fields + (fi -> eip))}
        case None => throw StuckError(e)
      }

        /***** New cases for Lab 5.  */
      case Assign(e1, e2) if isLValue(e1) => step(e2) map {e2p => Assign(e1,e2p)}
      case Assign(e1, e2) => step(e1) map {e1p => Assign(e1p,e2)}

      /* Everything else is a stuck error. */
      case _ => throw StuckError(e)
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