package main

import (
	"fmt"
	"strconv"
    "unicode"
)

// Simple imperative language

/*
vars       Variable names, start with lower-case letter

prog      ::= block
block     ::= "{" statement "}"
statement ::=  statement ";" statement           -- Command sequence
            |  vars ":=" exp                     -- Variable declaration
            |  vars "=" exp                      -- Variable assignment
            |  "while" exp block                 -- While
            |  "if" exp block "else" block       -- If-then-else
            |  "print" exp                       -- Print

exp ::= 0 | 1 | -1 | ...     -- Integers
     | "true" | "false"      -- Booleans
     | exp "+" exp           -- Addition
     | exp "*" exp           -- Multiplication
     | exp "||" exp          -- Disjunction
     | exp "&&" exp          -- Conjunction
     | "!" exp               -- Negation
     | exp "==" exp          -- Equality test
     | exp "<" exp           -- Lesser test
     | "(" exp ")"           -- Grouping of expressions
     | vars                  -- Variables
*/
// Values

type Kind int

const (
	ValueInt  Kind = 0
	ValueBool Kind = 1
	Undefined Kind = 2
)

type Val struct {
	flag Kind
	valI int
	valB bool
}

func mkInt(x int) Val {
	return Val{flag: ValueInt, valI: x}
}
func mkBool(x bool) Val {
	return Val{flag: ValueBool, valB: x}
}
func mkUndefined() Val {
	return Val{flag: Undefined}
}

func showVal(v Val) string {
	var s string
	switch {
	case v.flag == ValueInt:
		s = Num(v.valI).pretty()
	case v.flag == ValueBool:
		s = Bool(v.valB).pretty()
	case v.flag == Undefined:
		s = "Undefined"
	}
	return s
}

// Types

type Type int

const (
	TyIllTyped Type = 0
	TyInt      Type = 1
	TyBool     Type = 2
)

func showType(t Type) string {
	var s string
	switch {
	case t == TyInt:
		s = "Int"
	case t == TyBool:
		s = "Bool"
	case t == TyIllTyped:
		s = "Illtyped"
	}
	return s
}

// Value State is a mapping from variable names to values
type ValState map[string]Val

// Value State is a mapping from variable names to types
type TyState map[string]Type

// Interface

type Exp interface {
	pretty() string
	eval(s ValState) Val
	infer(t TyState) Type
}

type Stmt interface {
	pretty() string
	eval(s ValState)
	check(t TyState) bool
}

// Statement cases (incomplete)

type Seq [2]Stmt   // Command Sequence
type Decl struct { // Variable declaration
	lhs string
	rhs Exp
}
type IfThenElse struct { // If-then-else
	cond     Exp
	thenStmt Stmt
	elseStmt Stmt
}

type Assign struct { // Variable assignment
	lhs string
	rhs Exp
}

// Solution: statement cases

type While struct { // While
	cond   Exp
	doStmt Stmt
}

type Print struct { // Print
	exp Exp
}

// Expression cases (incomplete)

type Bool bool   // Boolean
type Num int     // Integer
type Mult [2]Exp // Multiplication
type Plus [2]Exp // Addition
type And [2]Exp  // Conjunction
type Or [2]Exp   // Disjunction
type Var string  // Variable

// Solution: expression cases

type Neg [1]Exp    // Negation
type Equal [2]Exp  // Equality test
type Lesser [2]Exp // Lesser test
type Group [1]Exp  // Grouping of expressions

/////////////////////////
// Stmt instances

// pretty print

func (stmt Seq) pretty() string {
	return stmt[0].pretty() + "; " + stmt[1].pretty()
}

func (decl Decl) pretty() string {
	return decl.lhs + " := " + decl.rhs.pretty()
}

// Solution: pretty print statements

func (assign Assign) pretty() string {
	return assign.lhs + " = " + assign.rhs.pretty()
}

func (ite IfThenElse) pretty() string {
	return "if( " + ite.cond.pretty() + " ) {\n    " + ite.thenStmt.pretty() + "\n} else {\n    " + ite.elseStmt.pretty() + "\n}"
}

func (whl While) pretty() string {
	return "while(" + whl.cond.pretty() + " ) {\n    " + whl.doStmt.pretty() + "\n}"
}

func (prnt Print) pretty() string {
	return "Print(" + prnt.exp.pretty() + ")"
}

// eval

func (stmt Seq) eval(s ValState) {
	stmt[0].eval(s)
	stmt[1].eval(s)
}

func (ite IfThenElse) eval(s ValState) {
	v := ite.cond.eval(s)
    if v.flag == ValueBool {
		switch {
		case v.valB:
			ite.thenStmt.eval(s)
  		case !v.valB:
			ite.elseStmt.eval(s)
    }

	} else {
		fmt.Printf("if-then-else eval fail")
	}

}

// Maps are represented via points.
// Hence, maps are passed by "reference" and the update is visible for the caller as well.
func (decl Decl) eval(s ValState) {
	v := decl.rhs.eval(s)
	x := (string)(decl.lhs)
	s[x] = v
}

// Solution eval statements


/*
 * Eval for assignment is the same as for declaration.
 * The Variable-Value Table s is updated with the new value
 */
func (assign Assign) eval(s ValState) {
    v := assign.rhs.eval(s)
    x := (string)(assign.lhs)
    s[x] = v
}

/*
 * To simulate a while-loop, the evaluation uses a for-loop.
 * In every iteration the condition is checked.
 * If the condition holds, the doStmt is evaluated.
 * That can be any statement that's described on top in the imp.
 * Otherwise the end of loop is reached and exited via break.
 */
func (whl While) eval(s ValState) {
    for{
        v := whl.cond.eval(s)
        if v.flag == ValueBool && v.valB == true {
            whl.doStmt.eval(s)
        }else{
            break
        }
    }
}

/*
 * Evaluation for the print statement evaluates the expression
 * and prints it's value via fmt.Printf
 */
func (prnt Print) eval(s ValState) {
    v := prnt.exp.eval(s)
    fmt.Printf("%s\n", showVal(v))
}

// type check

func (stmt Seq) check(t TyState) bool {
	if !stmt[0].check(t) {
		return false
	}
	return stmt[1].check(t)
}

/*
 * Check whether or not the type of the assigned expression isn't illtyped
 */
func (decl Decl) check(t TyState) bool {
	ty := decl.rhs.infer(t)
	if ty == TyIllTyped {
		return false
	}

	x := (string)(decl.lhs)
	t[x] = ty
	return true
}

/*
 * Check if the new type is the same as the type the variable a is currently holding.
 */
func (a Assign) check(t TyState) bool {
	x := (string)(a.lhs)
	return t[x] == a.rhs.infer(t)
}

// Solution: type check statements

/*
 * The condition of the while-loop must habe the type bool.
 * Hence the check return false it that's not the case.
 * Only if the condition is an boolean the check return true.
 */
func (whl While) check(t TyState) bool {
	ty := whl.cond.infer(t)
	if ty == TyBool{
		return true
	}
	return false
}

/*
 * The condition of the while-loop must habe the type bool.
 * Hence the check return false it that's not the case.
 * Only if the condition is an boolean the check return true.
 */
func (ite IfThenElse) check(t TyState) bool {
	ty := ite.cond.infer(t)
	if ty == TyBool{
		return true
	}
	return false
}

/*
 * To print an expression it must be have an actual type.
 * The check doesn't hold if the type is illtyped.
 * Otherwise the check is ok. There is no need to check
 * for bool or integer especially. Other types might be
 * added in the future, and this way the check doesn't
 * need to be modified.
 */
func (prnt Print) check(t TyState) bool {
	ty := prnt.exp.infer(t)
	if ty == TyIllTyped {
		return false
	}
	return true
}

/////////////////////////
// Exp instances

// pretty print

func (x Var) pretty() string {
	return (string)(x)
}

func (x Bool) pretty() string {
	if x {
		return "true"
	} else {
		return "false"
	}

}

func (x Num) pretty() string {
	return strconv.Itoa(int(x))
}

func (e Mult) pretty() string {

	var x string
	x = "("
	x += e[0].pretty()
	x += "*"
	x += e[1].pretty()
	x += ")"

	return x
}

func (e Plus) pretty() string {

	var x string
	x = "("
	x += e[0].pretty()
	x += "+"
	x += e[1].pretty()
	x += ")"

	return x
}

func (e And) pretty() string {

	var x string
	x = "("
	x += e[0].pretty()
	x += "&&"
	x += e[1].pretty()
	x += ")"

	return x
}

func (e Or) pretty() string {

	var x string
	x = "("
	x += e[0].pretty()
	x += "||"
	x += e[1].pretty()
	x += ")"

	return x
}

// Solution: pretty print exp

func (e Neg) pretty() string {

	var x string
	x = "("
	x += "!"
	x += e[0].pretty()
	x += ")"

	return x
}

func (e Equal) pretty() string {

	var x string
	x = "("
	x += e[0].pretty()
	x += " == "
	x += e[1].pretty()
	x += ")"

	return x
}

func (e Lesser) pretty() string {

	var x string
	x = "("
	x += e[0].pretty()
	x += " < "
	x += e[1].pretty()
	x += ")"

	return x
}

func (e Group) pretty() string {
	var x string
	x = "("
	x += e[0].pretty()
	x += ")"

	return x
}

// Evaluator

func (x Bool) eval(s ValState) Val {
	return mkBool((bool)(x))
}

func (x Num) eval(s ValState) Val {
	return mkInt((int)(x))
}

func (e Mult) eval(s ValState) Val {
	n1 := e[0].eval(s)
	n2 := e[1].eval(s)
	if n1.flag == ValueInt && n2.flag == ValueInt {
		return mkInt(n1.valI * n2.valI)
	}
	return mkUndefined()
}

func (e Plus) eval(s ValState) Val {
	n1 := e[0].eval(s)
	n2 := e[1].eval(s)
	if n1.flag == ValueInt && n2.flag == ValueInt {
		return mkInt(n1.valI + n2.valI)
	}
	return mkUndefined()
}

func (e And) eval(s ValState) Val {
	b1 := e[0].eval(s)
	b2 := e[1].eval(s)
	switch {
	case b1.flag == ValueBool && b1.valB == false:
		return mkBool(false)
	case b1.flag == ValueBool && b2.flag == ValueBool:
		return mkBool(b1.valB && b2.valB)
	}
	return mkUndefined()
}

func (e Or) eval(s ValState) Val {
	b1 := e[0].eval(s)
	b2 := e[1].eval(s)
	switch {
	case b1.flag == ValueBool && b1.valB == true:
		return mkBool(true)
	case b1.flag == ValueBool && b2.flag == ValueBool:
		return mkBool(b1.valB || b2.valB)
	}
	return mkUndefined()
}

// Solution: evaluator expressions

/*
 * A variable is a string consisting of it's own name.
 * The Variable-Table s is searched for the variable e.
 * If there is a value and it's ok the evaluation returns
 * the actual value of the variable. Otherwise it's undefined.
 */
func (e Var) eval(s ValState) Val {
    y := (string)(e)

//     if !isVarNameCorrect(y) {
//         fmt.Printf(" Syntax Error: Variable Name should start with a lowercase letter")
//         return mkUndefined()
//     }

    val, ok := s[y]
    if !ok {
        return mkUndefined()
    }else{
        if val.flag == ValueInt {
            return mkInt(s[y].valI)
        }
        
        if val.flag == ValueBool {
            return mkBool(s[y].valB)
        }
    }
    
    return mkUndefined()
}

/*
 * A negation consists of one Expression. 
 * Only booleans can be negated.
 * If the flag of the expression is an bool
 * the value is flipped and a new bool returned.
 * If the expression is not an boolean, the value
 * is undefined.
 */
func (e Neg) eval(s ValState) Val {
	n1 := e[0].eval(s)
	switch {
	case n1.flag == ValueBool && n1.valB == true:
		return mkBool(false)
	case n1.flag == ValueBool && n1.valB == false:
		return mkBool(true)
	}
	return mkUndefined()
}

/*
 * Both operands of the equals expression has to be from
 * the same type. Integer can't be compared to booleans.
 * If both are from the same type they're compared and
 * the result of the comparision is returned.
 * Aren't both operands from the same type the result is undefined.
 */
func (e Equal) eval(s ValState) Val {
	n1 := e[0].eval(s)
	n2 := e[1].eval(s)

	switch {
	case n1.flag == ValueBool && n2.flag == ValueBool:
		if n1 == n2 {
			return mkBool(true)
		} else {
			return mkBool(false)
		}

	case n1.flag == ValueInt && n2.flag == ValueInt:
		if n1 == n2 {
			return mkBool(true)
		} else {
			return mkBool(false)
		}
	}
	return mkUndefined()
}

/*
 * Both operands of the lesser expression has to be from
 * the same type. Integer can't be compared to booleans.
 * If both are from the same type they're compared and
 * the result of the comparision is returned.
 * Aren't both operands from the same type the result is undefined.
 */
func (e Lesser) eval(s ValState) Val {
	n1 := e[0].eval(s)
	n2 := e[1].eval(s)

	if n1.flag == ValueInt && n2.flag == ValueInt {
		return mkBool(n1.valI < n2.valI)
	}
	return mkUndefined()
}

// Type inferencer/checker

func (x Var) infer(t TyState) Type {
	y := (string)(x)
	ty, ok := t[y]
	if ok {
		return ty
	} else {
		return TyIllTyped // variable does not exist yields illtyped
	}

}

func (x Bool) infer(t TyState) Type {
	return TyBool
}

func (x Num) infer(t TyState) Type {
	return TyInt
}

func (e Mult) infer(t TyState) Type {
	t1 := e[0].infer(t)
	t2 := e[1].infer(t)
	if t1 == TyInt && t2 == TyInt {
		return TyInt
	}
	return TyIllTyped
}

func (e Plus) infer(t TyState) Type {
	t1 := e[0].infer(t)
	t2 := e[1].infer(t)
	if t1 == TyInt && t2 == TyInt {
		return TyInt
	}
	return TyIllTyped
}

func (e And) infer(t TyState) Type {
	t1 := e[0].infer(t)
	t2 := e[1].infer(t)
	if t1 == TyBool && t2 == TyBool {
		return TyBool
	}
	return TyIllTyped
}

func (e Or) infer(t TyState) Type {
	t1 := e[0].infer(t)
	t2 := e[1].infer(t)
	if t1 == TyBool && t2 == TyBool {
		return TyBool
	}
	return TyIllTyped
}

// Solution: type inferencer/checker

/*
 * The type must be a boolean for a negation.
 * If that's the case the type TyBool is returned.
 * Otherwise it's illtyped.
 */
func (e Neg) infer(t TyState) Type {
	t1 := e[0].infer(t)
	if t1 == TyBool {
		return TyBool
	}
	return TyIllTyped

}

/*
 * To compare two operands, they have to be from the same type.
 * The return type of the expression equal is always a boolean
 * if both operands can be compared. Otherwise it's illtyped.
 */
func (e Equal) infer(t TyState) Type {
	t1 := e[0].infer(t)
	t2 := e[1].infer(t)
	if t1 == TyBool && t2 == TyBool {
		return TyBool
	}
	if t1 == TyInt && t2 == TyInt {
		return TyBool
	}
	return TyIllTyped
}

/*
 * To compare two operands, they have to be from the same type.
 * In the case of lesser, it's neccessary that they're integer.
 * Booleans can't be compared with the lesser expression and
 * other types aren't implemented in this imp, aside from integesers.
 * That might change in the future and all types
 * that can be compared by the lesser expression need to be
 * added in this inferencer.
 * The return type of the expression equal is always a boolean
 * if both operands can be compared. Otherwise it's illtyped.
 */

func (e Lesser) infer(t TyState) Type {
	t1 := e[0].infer(t)
	t2 := e[1].infer(t)
	if t1 == TyInt && t2 == TyInt {
		return TyBool
	}
	return TyIllTyped
}

// Helper functions to build ASTs by hand

func number(x int) Exp {
	return Num(x)
}

func boolean(x bool) Exp {
	return Bool(x)
}

func plus(x, y Exp) Exp {
	return (Plus)([2]Exp{x, y})

	// The type Plus is defined as the two element array consisting of Exp elements.
	// Plus and [2]Exp are isomorphic but different types.
	// We first build the AST value [2]Exp{x,y}.
	// Then cast this value (of type [2]Exp) into a value of type Plus.

}

func mult(x, y Exp) Exp {
	return (Mult)([2]Exp{x, y})
}

func and(x, y Exp) Exp {
	return (And)([2]Exp{x, y})
}

func or(x, y Exp) Exp {
	return (Or)([2]Exp{x, y})
}

// Solution: helper functions

func neg(x Exp) Exp {
	return (Neg)([1]Exp{x})
}

func less(x, y Exp) Exp {
	return (Lesser)([2]Exp{x, y})
}

func equal(x, y Exp) Exp {
	return (Equal)([2]Exp{x, y})
}

// Examples

func run(e Exp) {
	s := make(map[string]Val)
	t := make(map[string]Type)
	fmt.Printf("\n ******* ")
	fmt.Printf("\n %s", e.pretty())
	fmt.Printf("\n %s", showVal(e.eval(s)))
	fmt.Printf("\n %s", showType(e.infer(t)))
	fmt.Printf("\n\n\n")
}

//  ((1*2)+0)
//  2
//  Int
func ex1() {
	fmt.Printf(" ex1:")
	ast := plus(mult(number(1), number(2)), number(0))
	run(ast)
}

//  (false&&0)
//  false
//  Illtyped
func ex2() {
	fmt.Printf(" ex2:")
	ast := and(boolean(false), number(0))
	run(ast)
}

//  (false||0)
//  Undefined
//  Illtyped
func ex3() {
	fmt.Printf(" ex3:")
	ast := or(boolean(false), number(0))
	run(ast)
}

// Solution: examples

//  (!true)
//  false
//  Bool
func testNeg1() {
	fmt.Print("Test neg 1:")
	ast := neg(boolean(true))
	run(ast)
}

//  (!(true&&false))
//  true
//  Bool
func testNeg2() {
	fmt.Print("Test neg 2:")
	ast := neg(and(boolean(true), boolean(false)))
	run(ast)
}

//  (!(false&&true))
//  true
//  Bool
func testNeg3() {
	fmt.Print("Test neg 3:")
	ast := neg(and(boolean(false), boolean(true)))
	run(ast)
}

//  (!(true||true))
//  false
//  Bool
func testNeg4() {
	fmt.Print("Test neg 4:")
	ast := neg(or(boolean(true), boolean(true)))
	run(ast)
}

//  (3 < 4)
//  true
//  Bool
func testLesser1() {
	fmt.Print("Test lesser 1:")
	ast := less(number(3), number(4))
	run(ast)
}

//  (4 < 4)
//  false
//  Bool
func testLesser2() {
	fmt.Print("Test lesser 2:")
	ast := less(number(4), number(4))
	run(ast)

}

//  (4 < 2)
//  false
//  Bool
func testLesser3() {
	fmt.Print("Test lesser 3:")
	ast := less(number(4), number(2))
	run(ast)

}

//  ((!true) == (4 < 6))
//  false
//  Bool
func testEq1() {
	fmt.Print("Test Equals 1:")
	ast := equal(neg(boolean(true)), less(number(4), number(6)))
	run(ast)
}

//  ((!true) == (6 < 6))
//  true
//  Bool
func testEq2() {
	fmt.Print("Test Equals 2:")
	ast := equal(neg(boolean(true)), less(number(6), number(6)))
	run(ast)
}

//  ((true&&(true&&false)) == (true||false))
//  false
//  Bool
func testEq3() {
	fmt.Print("Test Equals3:")
	ast := equal(and(boolean(true), and(boolean(true), boolean(false))), or(boolean(true), boolean(false)))
	run(ast)
}

//  ((!true)||false)
//  false
//  Bool
func testimp() {
	fmt.Print("Test implication with or and not")
	ast := or(neg(boolean(true)), boolean(false))
	run(ast)
}

//  (true&&2)
//  Undefined
//  Illtyped
func testError1() {
	fmt.Print("Test Error handling:")
	ast := and(boolean(true), number(2))
	run(ast)
}

//  (false < 4)
//  Undefined
//  Illtyped
func testError2() {
	fmt.Print("Test Error handling!")
	ast := less(boolean(false), number(4))
	run(ast)
}

//  (1 == true)
//  Undefined
//  Illtyped
func testError3() {
	fmt.Print("Test Error handling!")
	ast := equal(number(1), boolean(true))
	run(ast)
}


// Helper function to test statements

/*
 * Creates an expression Var and returns it.
 */
func variable(x string) Exp {
    return Var(x)
}

/*
 * Creates a declaration structure and updates the lookup-tables s and t.
 * Only if the check of the type holds, the value is assigned to the variable.
 */
func declVar(x string, y Exp, s ValState, t TyState) *Decl{    
    declVar := Decl{lhs: x, rhs: y}
    if declVar.check(t){
        declVar.eval(s)
        return &declVar
    }
    return nil
    
}

/*
 * Creates a assign structure and updated the lookup-tables s and t.
 * Only if the check of the type holds, the value is assigned to the variable.
 * The new type must be the same as the type of the value the variable is currently holding.
 */
func assignVar(x string, y Exp, s ValState, t TyState) *Assign {
    assignVar := Assign{lhs: x, rhs: y}
    if assignVar.check(t) {
        assignVar.eval(s)
        return &assignVar
    } 
    return nil
    
}

/*
 * Function for testing while statement.
 * The following structure is tested.

    while((testVariable < 10) ) {
        Print(testVariable); testVariable = (testVariable+1)
    }

 * As long as the testVariable is less than 10, the
 * value of the variable is printed via the print statement
 * and then the value is increased by 1.
 * That's also the abort condition of the while loop.
 * The doStmt statement is a commmand sequence statement.
 * It's an array consisting the two statement belonging to
 * a command sequence separated by ;.
 */

func testWhile() {
    s := make(map[string]Val)
	t := make(map[string]Type)
	fmt.Print("Test While!")
    fmt.Printf("\n ******* \n")
    
    max := number(10)
    nameString := "testVariable"
    
    varName := variable(nameString)
    index := declVar(varName.pretty(), number(0), s, t)
    
    cond := less(varName, max)
    
    prntStmt := Print{exp: varName}
    assignStmt := assignVar(varName.pretty(), plus(varName, number(1)), s, t)
	doStmt := Seq{prntStmt, assignStmt}
    
    whl := While{cond: cond, doStmt: doStmt}
    
    fmt.Printf("\n %s\n ", index.pretty())
    fmt.Printf("\n %s\n", whl.pretty())

    whl.eval(s)
    
    fmt.Printf("\n\n\n")     
    
}


/*
 * Function to test the if-then-else statement.
 * The following structure is tested:
    
    // if( (200 < 100) ) {
    if( (100 < 200) ) {
        testVariable = 100
    } else {
        testVariable = 200
    }
    
 * To print the result of the test, part of the evaluation
 * (ite.cond.eval(s).valB) is copied to get the right result. 
 */
func testIfThenElse() {
    s := make(map[string]Val)
	t := make(map[string]Type)
	fmt.Print("Test If-Then-Else!")
    fmt.Printf("\n ******* \n")
    
    nameString := "testVariable"
    
    varName := variable(nameString)    
    varValue := number(2)
    decl := declVar(varName.pretty(), varValue, s, t)
    
    newValue1 := number(100)
    assign1 := assignVar(decl.lhs, newValue1, s, t)
    
    newValue2 := number(200)
    assign2 := assignVar(decl.lhs, newValue2, s, t)
    
    cond := less(number(100), number(200))
    thenStmt := assign1
	elseStmt := assign2
        
    ite := IfThenElse{cond: cond, thenStmt: thenStmt, elseStmt: elseStmt}
    
    if ite.check(t){
        ite.eval(s)
        fmt.Printf("\n %s", ite.pretty())
        
//         testVariable = 100
        if ite.cond.eval(s).valB {
            fmt.Printf("\n %s", assign1.pretty())
        }else{
            fmt.Printf("\n %s", assign2.pretty())            
        }
        
//         Int
        fmt.Printf("\n %s", showType(varName.infer(t)))
    }
    fmt.Printf("\n\n\n")     

    
    cond = less(number(200), number(100))        
    ite = IfThenElse{cond: cond, thenStmt: thenStmt, elseStmt: elseStmt}
    
    if ite.check(t){
        ite.eval(s)
        fmt.Printf("\n %s", ite.pretty())

//         testVariable = 200
        if ite.cond.eval(s).valB {
            fmt.Printf("\n %s", assign1.pretty())
        }else{
            fmt.Printf("\n %s", assign2.pretty())            
        }
        
//         Int        
        fmt.Printf("\n %s", showType(varName.infer(t)))
    }
    fmt.Printf("\n\n\n") 
    
}

/*
 * Function for testing the assign statement
 * A new variable is created via variable() and
 * then declareted with a value.
 * The variable is then assigned new values.
 * If the assignment was successfull the result
 * of the assignment is printed. Otherwise an info
 * is printed, that the assignment wasn't possible.
 */
func testAssign() {
    s := make(map[string]Val)
	t := make(map[string]Type)
	fmt.Print("Test var Assignment!")
    fmt.Printf("\n ******* \n")
    
    nameString := "testVariable"
    
    varName := variable(nameString)    
    varValue := number(2)
    decl := declVar(varName.pretty(), varValue, s, t)
    if decl != nil {
        fmt.Printf("\n %s", decl.pretty())
        fmt.Printf("\n %s", showVal(varName.eval(s)))
        fmt.Printf("\n %s", showType(varName.infer(t)))
    }else{
        fmt.Printf("\n declaration not possible \n")
    }
    
    fmt.Printf("\n\n\n") 

    newValue := number(3)
    assign := assignVar(varName.pretty(), newValue, s, t)
    if assign != nil {
        fmt.Printf("\n %s", assign.pretty())
        fmt.Printf("\n %s", showVal(varName.eval(s)))
        fmt.Printf("\n %s", showType(varName.infer(t)))
    }else{
        fmt.Printf("\n Assignment not possible \n")
    }
    
    fmt.Printf("\n\n\n") 
    
    
    newValue = boolean(true)
    assign = assignVar(varName.pretty(), newValue, s, t)
    if assign != nil {
        fmt.Printf("\n %s", assign.pretty())
        fmt.Printf("\n %s", showVal(varName.eval(s)))
        fmt.Printf("\n %s", showType(varName.infer(t)))
    }else{
        fmt.Printf("\n Assignment not possible: %s \n", newValue.pretty())
    }
    
    fmt.Printf("\n\n\n") 

}

/*
 * Function for testing the declaration statement.
 * A variable is created with variable() and
 * declareted in the next step with the creation
 * of a declaration struct. The lookup-maps s and t
 * are updated as well. If the declaration was
 * successfull in declVar(), the declaration itself
 * is printed as well as the value and the type
 * of the new variable. Otherwise an info is printed,
 * that the declaration was not possible.
 */

func testDecl() {
    s := make(map[string]Val)
	t := make(map[string]Type)
	fmt.Print("Test var declaration!")
    fmt.Printf("\n ******* \n")
    
    nameString := "testVariable"
    varName := variable(nameString)    
    
    varValue := number(2)
    decl := declVar(varName.pretty(), varValue, s, t)
    if decl != nil{
        fmt.Printf("\n %s", decl.pretty())
        fmt.Printf("\n %s", showVal(varName.eval(s)))
        fmt.Printf("\n %s", showType(varName.infer(t)))
    }else {
        fmt.Printf("\n Declaration not possible \n")
    }
    
    fmt.Printf("\n\n\n")
    varValue = boolean(true)
    decl = declVar(varName.pretty(), varValue, s, t)
    if decl != nil{
        fmt.Printf("\n %s", decl.pretty())
        fmt.Printf("\n %s", showVal(varName.eval(s)))
        fmt.Printf("\n %s", showType(varName.infer(t)))   
    }else {
        fmt.Printf("\n Declaration not possible \n")
    }

    fmt.Printf("\n\n\n")
    varValue = equal(neg(boolean(true)), less(number(4), number(6)))
    decl = declVar(varName.pretty(), varValue, s, t)
    if decl != nil{
        fmt.Printf("\n %s", decl.pretty())
        fmt.Printf("\n %s", showVal(varName.eval(s)))
        fmt.Printf("\n %s", showType(varName.infer(t))) 
    }else {
        fmt.Printf("\n Declaration not possible \n")
    }

    fmt.Printf("\n\n\n")
    varValue = equal(neg(boolean(true)), number(2))
    decl = declVar(varName.pretty(), varValue, s, t)
    if decl != nil{
        fmt.Printf("\n %s", decl.pretty())
        fmt.Printf("\n %s", showVal(varName.eval(s)))
        fmt.Printf("\n %s", showType(varName.infer(t)))
        fmt.Printf("\n\n\n")    
    }else {
        fmt.Printf("\n Declaration not possible: %s \n", varValue.pretty())
    }

    fmt.Printf("\n\n\n")
}

/*
 * Creates a expression varName from type Var via the helper function variable()
 * The value and type of that variable is then printed. Since it's not declared
 * with any value, there should no value and type in s and t.
 */
func testVar() {
    s := make(map[string]Val)
	t := make(map[string]Type)
	fmt.Print("Test Var!")
    fmt.Printf("\n ******* \n")
    
    nameString := "testVariable"
    
    varName := variable(nameString)
    
    // Undefined
    fmt.Printf("\n %s", showVal(varName.eval(s)))
    
    // Illtyped
    fmt.Printf("\n %s", showType(varName.infer(t)))
    
    fmt.Printf("\n\n\n")    
}

// ----------------

func main() {

	fmt.Printf("\n")
	ex1()
	ex2()
	ex3()
	testNeg1()
	testNeg2()
	testNeg3()
	testNeg4()
	testLesser1()
	testLesser2()
	testLesser3()
	testEq1()
	testEq2()
	testEq3()
	testimp()
	testError1()
	testError2()
	testError3()
    testVar()
    testDecl()
    testAssign()
    testIfThenElse()
    testWhile()
}

func isVarNameCorrect(s string) bool {
   r := []rune(s)
//    fmt.Print(r[0])   
   if unicode.IsLetter(r[0]) && unicode.IsLower(r[0]) {
       return true
   }
   
   return false
}
