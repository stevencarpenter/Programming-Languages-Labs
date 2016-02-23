package jsy.student

object Lab3 extends jsy.util.JsyApplication {
  import jsy.lab3.Parser
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * <Your Name>
   * 
   * Partner: <Your Partner's Name>
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
      case S(s) => try s.toDouble catch {case e: Exception => Double.NaN}
      //case Function(_, _,_) => Double.NaN
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => {
        if((n == 0) || (n.isNaN == true)) false
        else true
      } 
      case S(s) => s match {
        case "" => false
        case _ => true
      }
      case Undefined => false
      case Function(_, _, _) => true
      //case _ => ???
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
        // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
        // of the function (from the input program).
      case N(n) => pretty(N(n))
      case B(b) => b match {
        case true => "true"
        case false => "false"
      }
      case Undefined => "Undefined"
      case Function(_, _, _) => "function"
      //case _ => ???
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
        case (S(v1), S(v2)) => (bop: @unchecked) match {
          case Le => v1 <= v2
          case Lt => v1 < v2
          case Gt => v1 > v2
          case Ge => v1 >= v2
        }
        case _ => (bop: @unchecked) match {
          case Le => toNumber(v1) <= toNumber(v2)
          case Lt => toNumber(v1) < toNumber(v2)
          case Gt => toNumber(v1) > toNumber(v2)
          case Ge => toNumber(v1) >= toNumber(v2)
        }
      }
      //case _ => ???

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
      // if and Var
      case _ if (isValue(e)) => e
      case N(n) => N(n)
      case B(b) => B(b)
      case S(s) => S(s)
      case If(e1, e2, e3) => {
        if (toBoolean(eval(env, e1))) eval(env, e2)
        else eval(env, e3)
      }
      case Var(x) => eval(env, get(env, x))
      //unary ops
      case Unary(Neg, e) => N(- toNumber(eToVal(e)))
      case Unary(Not, e) => B(!toBoolean(eToVal(e)))
      case ConstDecl(x, e1, e2) => eval(extend(env, x, eToVal(e1)), e2)
      /*case ConstDecl(x, e1, e2) => {
        val newEnv = extend(env, x, eval(env, e1))
        eval(newEnv, e2)
      }
      */

      //BINARY OPS
      case Binary(bop,e1,e2) => {
        bop match {
          case Plus => (eToVal(e1), eToVal(e2)) match {
            case (S(s1), v2) => S(s1 + toStr(v2))
            case (v1, S(s2)) => S(toStr(v1) + s2)
            case (v1, v2) => N(toNumber(v1) + toNumber(v2))
          }
          case Minus => N(toNumber(eToVal(e1)) - toNumber(eToVal(e2)))
          case Times => N(toNumber(eToVal(e1)) * toNumber(eToVal(e2)))
          case Div => require(toNumber(eToVal(e1)) != 0) //cant divide zero into anything
            N(toNumber(eToVal(e1)) / toNumber(eToVal(e2)))

          case Eq => (eToVal(e1), eToVal(e2)) match {
            case (Function(_,_,_), _) => throw new DynamicTypeError(e)
            case (_, Function(_,_,_)) => throw new DynamicTypeError(e)
            case (S(s1), S(s2)) => B(s1 == s2)
            case (N(n1), N(n2)) => B(n1 == n2)
            case (B(b1), B(b2)) => B(b1 == b2)
            case (_,_) => throw new DynamicTypeError(e)//B(false)
          }
          case Ne => (eToVal(e1), eToVal(e2)) match {
            case (Function(_,_,_), _) => throw new DynamicTypeError(e)
            case (_, Function(_,_,_)) => throw new DynamicTypeError(e)
            case (S(s1), S(s2)) => B(s1 != s2)
            case (N(n1), N(n2)) => B(n1 != n2)
            case (B(b1), B(b2)) => B(b1 != b2)
            case (_,_) => throw new DynamicTypeError(e)
          }

          case Le => (eToVal(e1), eToVal(e2)) match{
            case (S(e1), S(e2)) => B(e1 <= e2)
            case (e1, e2) => B(toNumber(e1) <= toNumber(e2))
          }
          case Lt => (eToVal(e1), eToVal(e2)) match{
            case (S(e1), S(e2)) => B(e1 < e2)
            case (e1, e2) => B(toNumber(e1) < toNumber(e2))
          }
          case Ge => (eToVal(e1), eToVal(e2)) match{
            case (S(e1), S(e2)) => B(e1 <= e2)
            case (e1, e2) => B(toNumber(e1) >= toNumber(e2))
          }
          case Gt => (eToVal(e1), eToVal(e2)) match{
            case (S(e1), S(e2)) => B(e1 > e2)
            case (e1, e2) => B(toNumber(e1) > toNumber(e2))
          }

          case And => if(toBoolean(eToVal(e1)) == false) eToVal(e1) else eToVal(e2)
          case Or => if(toBoolean(eToVal(e1))) eToVal(e1) else eToVal(e2)
          case Seq => eval(env,e1)
            eval(env,e2)
        }
      }
      case Print(e1) => println(pretty(eToVal(e1))); Undefined
      case Call(e1, e2) => (eToVal(e1), eToVal(e2)) match {
        case (Function(None, x, ebody), v2) => eval(extend(env, x, v2), ebody)
        case (v1 @ Function(Some(p), x, ebody), v2) => eval(extend(extend(env, x, v2), p, v1), ebody)
        case (_, _) => throw new DynamicTypeError(e)
      }

      //case _ => ???
    }
    /*e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e
      case Var(x) => get(env, x)
      case _ if isValue(e) => e

      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

      case Unary(Neg, e1) => N(-eToN(e1))
      case Unary(Not, e1) => B(!eToB(e1))
      case Binary(bop @ (Lt|Le|Gt|Ge), e1, e2) => B(inequalityVal(bop, eToVal(e1), eToVal(e2)))

      case Binary(bop @ (Eq|Ne), Function(_,_,_), e2) => throw new DynamicTypeError(e)
      case Binary(bop @ (Eq|Ne), e1, Function(_,_,_)) => throw new DynamicTypeError(e)

      case Binary(Plus, e1, e2) => (eToVal(e1), eToVal(e2)) match {
        case (S(s1), v2) => S(s1 + toStr(v2))
        case (v1, S(s2)) => S(toStr(v1) + s2)
        case (v1, v2) => N(toNumber(v1) + toNumber(v2))
      }
      case Binary(Minus, e1, e2) => N(eToN(e1) - eToN(e2))
      case Binary(Times, e1, e2) => N(eToN(e1) * eToN(e2))
      case Binary(Div, e1, e2) => N(eToN(e1) / eToN(e2))

      case ConstDecl(x, e1, e2) => eval(extend(env, x, eToVal(e1)), e2)
      case Binary(And, e1, e2) => if(eToB(e1) == false) eToVal(e1) else eToVal(e2)
      case Binary(Or, e1, e2) => if(eToB(e1)) eToVal(e1) else eToVal(e2)
      case Binary(Seq, e1, e2) => eval(env,e1)
        eval(env,e2)


      case If(e1, e2, e3) => {
        if (toBoolean(eval(env, e1))) eval(env, e2)
        else eval(env, e3)
      }

      case Call(e1, e2) => (eToVal(e1), eToVal(e2)) match {
        case (Function(None, x, ebody), v2) => eval(extend(env, x, v2), ebody)
        case (v1 @ Function(Some(p), x, ebody), v2) => eval(extend(extend(env, x, v2), p, v1), ebody)
        case (_, _) => throw new DynamicTypeError(e)
      }

      case _ => throw new UnsupportedOperationException

        */
      /*case Call(e1,e2) => eToVal(e1) match {
        case Function(None,varName,fBody) =>
          eval(extend(env,varName,eToVal(e2)),fBody)

        case Function(Some(func),varName,fBody)=>
          val f1 = Function(Some(func),varName,fBody)
          val fun=extend(env,func,f1)
          eval(extend(fun, varName, eToVal(e2)), fBody)

        case _ => throw DynamicTypeError(e)
      }
*/

    }

    

  /* Small-Step Interpreter with Static Scoping */
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    /* Simple helper that calls substitute on an expression
     * with the input value v and variable name x. */
    def subst(e: Expr): Expr = substitute(e, v, x)
    /* Body */
    e match {
      case Unary(uop,e1) => Unary(uop,substitute(e1,v,x))
      case Binary(bop,e1,e2)=> Binary(bop,substitute(e1,v,x),substitute(e2,v,x))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Call(e1,e2) => Call(substitute(e1,v,x),substitute(e2,v,x))
      case Var(y) =>
        if(x==y) v
        else Var(y)
      case(Function(Some(func),varName,fBody)) =>
        if((x==func)||(x==varName)) Function(Some(func),varName,fBody)
        else Function(Some(func),varName,subst(fBody))
      case(Function(None,varName,fBody)) =>
        if(x==varName) Function(None,varName,fBody)
        else Function(None,varName,subst(fBody))
      case ConstDecl(y,e1,e2) =>
        if(x==y) ConstDecl(y,substitute(e1,v,x), e2)
        else ConstDecl(y,substitute(e1,v,x), substitute(e2,v,x))
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(subst(e1))
      case _ => throw new UnsupportedOperationException
    }
  }
    
  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined

      case Print(e1) => Print(step(e1))

      case Unary(Neg, v) => v match{
        case N(n) => N(-n)
        case _ => Unary(Neg,step(v))
    }
      case Unary(Not, v) => v match {
        case B(n) => B(!n)
        case _ => Unary(Not, step(v))
      }
      /* Inductive Cases: Search Rules */

      case Binary(bop@(Minus | Times | Div), v1, v2) if(isValue(v1) && !isValue(v2))  => {
        Binary(bop, v1, step(v2))

      }
      case Binary(bop@(Minus | Times | Div), v1, v2) if(!isValue(v1) && isValue(v2))  => {
        Binary(bop, step(v1), v2)

      }
      case Binary(bop@(Minus | Times | Div), v1, v2) if(!isValue(v1) && !isValue(v2))  => {
        Binary(bop, step(v1), step(v2))

      }


      case Binary(bop@(Minus | Times | Div), v1, v2) if(isValue(v1) && isValue(v2))  => {
        (bop: @unchecked) match {
          case Minus => N(toNumber(v1) - toNumber(v2))
          case Times => N(toNumber(v1) - toNumber(v2))
          case Div => N(toNumber(v1) - toNumber(v2))
        }
      }

      //case Binary(bop@(Minus | Times | Div), v1, v2) if(!isValue(v1)) => Binary(bop@(Minus | Times | Div), v1, v2)

      case Binary(bop@(Eq | Ne), v1, v2) if(!isValue(v1) && isValue(v2)) => Binary(bop, step(v1), v2)
      case Binary(bop@(Eq | Ne), v1, v2) if(isValue(v1) && !isValue(v2)) => Binary(bop, v1, step(v2))
      case Binary(bop@(Eq | Ne), v1, v2) if(!isValue(v1) && !isValue(v2)) => Binary(bop, step(v1), step(v2))

      case Binary(bop@(Eq | Ne), v1, v2) if(isValue(v1) && isValue(v2)) => (v1, v2) match {
        case (Function(_,_,_),_) => throw new DynamicTypeError(e)
        case (_,Function(_,_,_)) => throw new DynamicTypeError(e)
        case _ => {
          (bop: @unchecked) match {
            case Eq => B(toBoolean(v1) == toBoolean(v2))
            case Ne => B(toBoolean(v1) != toBoolean(v2))
          }
        }
      }


      case Binary(And, e1, e2) =>
        if (isValue(e1)) {
          if(toBoolean(e1)) e2
          else e1
        }
        else Binary(And, step(e1), e2)

      case Binary(Or, e1, e2) =>
        if (isValue(e1)) {
          if(toBoolean(e1)) e1
          else e2
        }
        else Binary(Or, step(e1), e2)

      case If(e1, e2, e3) =>
        if (isValue(e1))
        {
          if(toBoolean(e1)) e2
          else e3
        }
        else If(step(e1),e2,e3)

      case Binary(Plus,v1, v2 ) if(isValue(v1) && isValue(v2)) => (v1, v2) match {
        case (S(v1), S(v2)) => S(v1 + v2)
        case (S(v1), _) => S(v1 + toStr(v2))
        case (_, S(v2)) => S(toStr(v1) + v1)
        case (v1, v2) => N(toNumber(v1) + toNumber(v2))
      }
      //case Binary(Seq, v1, v2) if isValue()=> step(v1)
        //step(v2)
      case Unary(uop, e1) => Unary(uop, step(e1))
      case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, step(e2))
      case Binary(bop, e1, e2)  => {
        val eprime = step(e1)
        Binary(bop, eprime, e2)
      }

      case Call(v1,v2) if (isValue(v1)&&isValue(v2)) =>
        v1 match {
          case Function(None, x, e1) => substitute(e1,v2,x)
          case Function(Some(x1),x,e1) => substitute(substitute(e1,v1,x1),v2,x)
          case _ => throw DynamicTypeError(e)
        }

      case Call(e1@Function(_,_,_),e2) =>
        val e2p=step(e2)
        Call(e1,e2p)

      case Call(v1,e2) if isValue(v1) =>
        throw DynamicTypeError(e)

      case Call(e1,e2) =>
        //val e1p=step(e1)
        Call(step(e1),e2)

              case Print(e1) => Print(step(e1))
      case Unary(uop,e1) => Unary(uop, step(e1))
      case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, step(e2))
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)
      case Call(Function(p, x, e1), e2) => Call(Function(p, x, e1), step(e2))
      case Call(e1, e2) => Call(step(e1), e2)

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
