package jsy.student

import java.lang.NumberFormatException

object Lab2 extends jsy.util.JsyApplication {
  import jsy.lab2.Parser
  import jsy.lab2.ast._

  /*
   * CSCI 3155: Lab 2
   * <Steven Carpenter>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the '???' expression with  your code in each function.
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
   * '???' as needed to get something  that compiles without error. The ???
   * is a Scala expression that throws the exception scala.NotImplementedError.
   *
   */

  /* We represent a variable environment as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */

  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }

  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   */
/*
  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(b) => b match{
        case true => 1
        case false => 0
      }
      case S(s) => try {s.toDouble}
        catch {case _: UnsupportedOperationException => Double.NaN}
      case Undefined => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => n match {
        case 0 => false
        case _ if n.isNaN() => false
        case _ => true //anything else that is a number is true
      }
      case S(s) => true //strings are true
      case _ => throw new UnsupportedOperationException
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case Undefined => "undefined"
      case B(b) => b.toString
      case N(n) => n match {
        case _ if n.isWhole() => "%0f" format n
        case _ => n.toString
      }
      case _ => throw new UnsupportedOperationException
    }
  }
*/
  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(n) => if (n == true) 1 else 0
      case S("")=> 0
      case S(s) => {
        try s.toDouble
        catch {
          case e:  Exception => Double.NaN
        }
      }
      case Undefined => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => {
        if ((n == 0) || (n.isNaN==true)) false
        else true
      }
      case S(s) => {
        if (s == "") false
        else true
      }
      case Undefined => false

    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case N(n) => pretty(N(n)) // doesn't produce 3[] by 3[.0]
      case B(b) => {
        if(b==true) "true"
        else "false"
      }
      case Undefined => "undefined"
      //case _ => ???
    }
  }




  def eval(env: Env, e: Expr): Expr = {
    /* Some helper functions for convenience. */
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
      case ConstDecl(x, e1, e2) => {
        val newEnv = extend(env, x, eval(env, e1))
        eval(newEnv, e2)
      }

        //BINARY OPS
      case Binary(bop,e1,e2) => {
        bop match {
          case Plus => N(toNumber(eToVal(e1)) + toNumber(eToVal(e2)))
          case Minus => N(toNumber(eToVal(e1)) - toNumber(eToVal(e2)))
          case Times => N(toNumber(eToVal(e1)) * toNumber(eToVal(e2)))
          case Div => require(toNumber(eToVal(e1)) != 0) //cant divide zero into anything
                        N(toNumber(eToVal(e1)) / toNumber(eToVal(e2)))

          case Eq => B((eToVal(e1)) == (eToVal(e2)))
          case Ne => B((eToVal(e1)) != (eToVal(e2)))

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

      //case _ => ???
    }

  }

  // Interface to run your interpreter starting from an empty environment.
  def eval(e: Expr): Expr = eval(emp, e)

  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def eval(s: String): Expr = eval(Parser.parse(s))

  /* Interface to run your interpreter from the command-line.  You can ignore what's below. */
  def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }

    val expr = Parser.parseFile(file)

    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }

    if (debug) { println("Evaluating ...") }

    val v = eval(expr)

     println(pretty(v))
  }

}
