;Timothy Kuo, Andrew Hwang, Faraz Ahmed

(load "classParser.scm")

;interprets the file for Java/C like program
(define interpret
  (lambda (filename classname)
    (call/cc
     (lambda (return)
       (executeMain
        (initialClassState (parser filename) '(()()) (list (parser filename)) '() (string->symbol classname) (string->symbol classname) (string->symbol classname))
        (list (parser filename)) (string->symbol classname) return (string->symbol classname) (string->symbol classname) (string->symbol classname))))))


(define insertClass
  (lambda (name closure state)
    (M_insert name closure state)))

;checks if parent class exists
(define hasParentClass?
  (lambda (parsetree)
    (if (pair? (caddr parsetree))
        #t
        #f)))

;gets parent class
(define getParentClass
  (lambda (parsetree)
    (car (cdaddr parsetree))))

(define classBody cadddr)

(define classClosure
  (lambda (parsetree state full_expression throw class this super)
    (if (hasParentClass? parsetree)
        (cons (initialState (classBody parsetree) state full_expression throw class this super) (cons (lookup (getParentClass parsetree) state this super) '()))
        (initialState (classBody parsetree) state full_expression throw class this super))))


(define initialClassState
  (lambda (parsetree state full_expression throw class this super)
    (cond
      ((null? parsetree) state)
      ((list? (operator parsetree)) (initialClassState (restOfExpression parsetree)
                                                       (initialClassState (operator parsetree) state full_expression throw class this super) full_expression throw class this super))
      ((eq? 'class (operator parsetree)) (insertClass (operand1 parsetree) (classClosure parsetree state full_expression throw (operand1 parsetree) this super) state))
      (else (initialClassState (restOfExpression parsetree) state full_expression throw class this super)))))



(define createNewInstance
  (lambda (full_expression state classname throw class this super)
    (cond
      ((null? full_expression) state)
      ((list? (operator full_expression)) (createNewInstance (restOfExpression full_expression) (createNewInstance (operator full_expression) state classname throw class this super)
                                                       classname throw class this super))
      ((eq? classname (operand1 full_expression)) (classClosure full_expression state full_expression throw class this super))
      (else (createNewInstance (restOfExpression full_expression) state classname throw class this super)))))
    
;getClass for left hand side of dot expression
(define getClass
  (lambda (expression state this super)
    (cond
      ((and (list? expression) (eq? 'new (operator expression))) (className expression))
      (else expression))))

 
(define getInstance
  (lambda (expression state this super)
    (cond
      ((and (list? expression) (eq? 'new (operator expression))) 'null)
      (else (car (lookup expression state this super))))))
     
;interprets the function inside its function environment
(define interpretFunc
  (lambda (funcBody funcEnv full_expression throw class this super)
    (call/cc
     (lambda (return)
       (pop (pop (M_state funcBody full_expression funcEnv return return return throw class this super)))))))

;executes the M_state function
(define executeMain
  (lambda (state full_expression classname return class this super)
    (M_state (lookup 'main (lookup classname state this super) this super)
             full_expression
             (push state) return return return '() class this super)))

;creates the initial/top-level state that contains global variables and functions with its values and closures respectively
(define initialState
  (lambda (parsetree state full_expression throw class this super)
    (cond
      ((null? parsetree) state)
      ((list? (operator parsetree)) (initialState (restOfExpression parsetree)
                                                  (initialState (operator parsetree) state full_expression throw class this super) full_expression throw class this super))
      ((or (eq? (operator parsetree) 'static-function) (eq? (operator parsetree) 'function))
       (funcInsert (funcName parsetree) (funcClosure (restOfFunc parsetree) class) state this super))
      ((eq? (operator parsetree) 'var) (M_declare parsetree full_expression state throw class this super))
      ((eq? (operator parsetree) '=) (M_assign parsetree full_expression state throw class this super))
      (else (initialState (restOfExpression parsetree) (initialState (currentExp parsetree) state full_expression throw class this super) full_expression throw class this super)))))


;determines the value of a mathematical expression, variables are allowed if they have already been declared and assigned
(define M_value
  (lambda (expression full_expression s throw class this super)
    (cond
      ((number? expression) expression)
      ((and (atom? expression) (eq? 'null (lookup expression s this super))) (error "using before assigning"))
      ((atom? expression) (lookup expression s this super))
      ((eq? 'true expression) #t) ;if true and false are in a list it is (operator expression)
      ((eq? 'false expression) #f) ;if true and false are in a list it is (operator expression) otherwise, if it's a string its expression
      ((eq? 'dot (operator expression)) (lookup expression s this super))
      ((eq? (operator expression) 'funcall) (callFunc (funcName expression) (getFuncEnv (getActualParams expression) (getFormalParams (funcName expression) s this super) (push s) full_expression throw class this super) full_expression throw class this super))
      ((eq? '+ (operator expression)) (+ (M_value (operand1 expression) full_expression s throw class this super) (M_value (operand2 expression) full_expression s throw class this super)))
      ((and (null? (checkOperand2 expression)) (eq? '- (operator expression))) (- 0 (M_value (operand1 expression) full_expression s throw class this super))) 
      ((eq? '- (operator expression)) (- (M_value (operand1 expression) full_expression s throw class this super) (M_value (operand2 expression) full_expression s throw class this super)))
      ((eq? '* (operator expression)) (* (M_value (operand1 expression) full_expression s throw class this super) (M_value (operand2 expression) full_expression s throw class this super)))
      ((eq? '/ (operator expression)) (quotient (M_value (operand1 expression) full_expression s throw class this super) (M_value (operand2 expression) full_expression s throw class this super)))
      ((eq? '% (operator expression)) (remainder (M_value (operand1 expression) full_expression s throw class this super) (M_value (operand2 expression) full_expression s throw class this super)))
      ((eq? '== (operator expression)) (boolean (eq? (M_value (operand1 expression) full_expression s throw class this super) (M_value (operand2 expression) full_expression s throw class this super))))
      ((eq? '!= (operator expression)) (boolean (not (eq? (M_value (operand1 expression) full_expression s throw class this super) (M_value (operand2 expression) full_expression s throw class this super)))))
      ((eq? '< (operator expression)) (boolean (< (M_value (operand1 expression) full_expression s throw class this super) (M_value (operand2 expression) full_expression s throw class this super))))
      ((eq? '> (operator expression)) (boolean (> (M_value (operand1 expression) full_expression s throw class this super) (M_value (operand2 expression) full_expression s throw class this super))))
      ((eq? '<= (operator expression)) (boolean (<= (M_value (operand1 expression) full_expression s throw class this super) (M_value (operand2 expression) full_expression s throw class this super))))
      ((eq? '>= (operator expression)) (boolean (>= (M_value (operand1 expression) full_expression s throw class this super) (M_value (operand2 expression) full_expression s throw class this super))))
      ((eq? '&& (operator expression)) (boolean (myAnd (M_value (operand1 expression) full_expression s throw class this super) (M_value (operand2 expression) full_expression s throw class this super))))
      ((eq? '|| (operator expression)) (boolean (myOr (M_value (operand1 expression) full_expression s throw class this super) (M_value (operand2 expression) full_expression s throw class this super))))
      ((eq? '! (operator expression)) (boolean (myNot (M_value (operand1 expression) full_expression s throw class this super))))
      ((eq? 'new (operator expression)) (createNewInstance full_expression '(()()) (operand1 expression) throw class this super)) ;TODO possible side effects
      ((eq? 'true (M_value expression full_expression s throw class this super)) 'true)
      ((eq? 'false (M_value expression full_expression s throw class this super)) 'false)
      (else (error 'unknown "unknown expression")))))


;returns the state after implementing the parse tree
(define M_state
  (lambda (parsetree full_expression state return break continue throw class this super)
    (cond
      ((null? parsetree) state)
      ((list? (operator parsetree)) (M_state (nextOperation parsetree) full_expression (M_state (operator parsetree) full_expression state return break continue throw class this super) return break continue throw class this super))
      ((or (eq? (operator parsetree) 'function) (eq? (operator parsetree) 'static-function)) (funcInsert (funcName parsetree) (funcClosure (restOfFunc parsetree) class) state this super))
      ((eq? (operator parsetree) 'funcall) (M_FuncState (funcName parsetree) (getFuncEnv (getActualParams parsetree) (getFormalParams (funcName parsetree) state this super) (push state) full_expression throw class this super) full_expression throw class this super))
      ;((eq? (operator parsetree) 'dot) (
      ((eq? (operator parsetree) 'while) (M_state_while (operand1 parsetree) full_expression (operand2 parsetree) state return throw class this super))
      ((and (eq? (operator parsetree) 'try) (null? (finally_body parsetree))) (pop (M_try (try_body parsetree) (cons parsetree full_expression) (push state) return break continue throw)))
      ((eq? (operator parsetree) 'try) (pop (M_try_finally (try_body parsetree) (cons parsetree full_expression) (push state) return break continue throw)))
      ((eq? (operator parsetree) 'var) (M_declare parsetree full_expression state throw class this super))
      ((and (singleState? state) (eq? (operator parsetree) 'continue)) (error "illegal continue"))
      ((eq? (operator parsetree) 'continue) (continue (pop state)))
      ((eq? (operator parsetree) 'begin) (pop (M_begin (restOfExpression parsetree) full_expression (push state) return break continue throw)))
      ((and (singleState? state) (eq? (operator parsetree) 'break)) (error "illegal break"))
      ((eq? (operator parsetree) 'break) (break (pop state)))
      ((and (eq? (operator parsetree) 'throw) (null? (catch_body (currentExp full_expression)))) (error "no catch"))
      ((and (pair? throw) (eq? (operator parsetree) 'throw)) ((currentThrow throw) (M_catch (currentExp full_expression) (restOfExpression full_expression) (M_insert 'random (M_value (operand1 parsetree) full_expression state throw) (push (pop state))) return break continue (restOfThrow throw))))
      ((eq? (operator parsetree) 'throw) (error "no where to throw"))
      ((eq? (operator parsetree) '=) (M_assign parsetree full_expression state throw class this super))
      ((eq? (operator parsetree) 'returnState) (return (state_changer (M_return parsetree full_expression state throw class this super) state)))
      ((eq? (operator parsetree) 'return) (return (M_return parsetree full_expression state throw class this super)))
      ((and (eq? (operator parsetree) 'if) (ifelse? parsetree)) (M_state_if_else (operand1 parsetree) full_expression (operand2 parsetree) (else parsetree) state return break continue throw class this super))
      ((eq? (operator parsetree) 'if) (M_state_if (operand1 parsetree) full_expression (operand2 parsetree) state return break continue throw class this super))
      (else (M_value parsetree full_expression state throw class this super)))))

;executes begin body
(define M_begin
  (lambda (expression full_expression state return break continue throw class this super)
    (cond
      ((null? expression) state)
      ((eq? (type expression) 'var) (M_begin (restOfExpression expression) full_expression (M_declare (declareVar expression) full_expression state throw class this super) return break continue throw class this super)) 
      (else (M_begin (restOfExpression expression) full_expression (M_state (currentExp expression) full_expression state return break continue throw class this super) return break continue throw class this super)))))

;interprets the function body within the scope of the function environment
(define M_FuncState
  (lambda (name funcEnv full_expression throw class this super)
    (if (eq? (operand1 name) 'this)
        (interpretFunc (modified_body (body (lookup name funcEnv this super))) funcEnv full_expression throw class this super)
        (interpretFunc (modified_body (body (lookup name funcEnv this super))) funcEnv full_expression throw class (lookup (operand1 name) funcEnv this super) super))))

;M_return returns the value of the expression
(define M_return
  (lambda (expression full_expression state throw class this super)
       (M_value (operand1 expression) full_expression state throw class this super)))

;execute try body
(define M_try
  (lambda (expression full_expression state return break continue oldthrow class this super)
    (call/cc
     (lambda (throw)
       (letrec ((loop (lambda (expression full_expression state return break continue throw class this super)
                        (cond
                          ((null? expression) state)
                          (else (loop (restOfExpression expression) full_expression (M_state (operator expression) full_expression state return break continue throw class this super) return break continue throw class this super))))))
         (loop expression full_expression state return break continue (cons throw oldthrow) class this super))))))

;execute try body if there is a finally body 
(define M_try_finally
  (lambda (expression full_expression state return break continue oldthrow class this super)
    (call/cc
     (lambda (throw)
       (letrec ((loop (lambda (expression full_expression state return break continue throw class this super)
                        (cond
                          ((null? expression) (M_finally (finally_body (currentExp full_expression)) full_expression (push (pop state)) return break continue throw class this super))
                          (else (loop (restOfExpression expression) full_expression (M_state (currentExp expression) full_expression state return break continue throw class this super) return break continue throw class this super))))))
         (loop expression full_expression state return break continue (cons throw oldthrow) class this super))))))

;execute catch body
(define M_catch
  (lambda (expression full_expression state return break continue throw class this super)
    (letrec ((loop (lambda (catch_expression full_expression state return break continue throw class this super)
              (cond
                ((and (null? catch_expression) (null? (finally_body expression))) state)
                ((null? catch_expression) (M_finally (finally_body expression) full_expression (push (pop state)) return break continue throw class this super))
                (else (loop (restOfExpression catch_expression) full_expression (M_state (currentExp catch_expression) full_expression state return break continue throw class this super) return break continue throw class this super))))))
      (loop (catch_finally_body (catch_body expression)) full_expression (M_insert (exception (catch_body expression)) (lookup 'random (getFirstLayer state) this super) (M_remove 'random state)) return break continue throw class this super))))

;execute finally body
(define M_finally
  (lambda (expression full_expression state return break continue throw class this super)
    (letrec ((loop (lambda (expression full_expression state return break continue throw class this super)
                     (cond
                       ((null? expression) state)
                       (else (loop (restOfExpression expression) full_expression (M_state (currentExp expression) full_expression state return break continue throw class this super) return break continue throw class this super))))))
      (loop (restOfExpression expression) full_expression state return break continue throw class this super))))

;M_state_while continually does the statement as long as the condition is true 
(define M_state_while
  (lambda (condition full_expression statement state return throw class this super)
    (call/cc
     (lambda (break)
       (letrec ((loop (lambda (condition full_expression statement state return break throw class this super)
                        (if (boolean2 (M_value condition full_expression state throw class this super))
                               (loop condition full_expression statement (M_state_while_stmt statement full_expression state return break throw class this super) return break throw class this super)
                               state))))
         (loop condition full_expression statement state return break throw class this super))))))

(define M_state_while_stmt
  (lambda (statement full_expression state return break throw class this super)
    (call/cc
     (lambda (continue)
       (M_state statement full_expression state return break continue throw class this super)))))

;M_state_if does the statement if the condition is true
(define M_state_if
  (lambda (condition full_expression statement state return break continue throw class this super)
    (if (boolean2 (M_value condition full_expression state throw class this super))
        (M_state statement full_expression state return break continue throw class this super)
         state)))

;M_state_if_else operates an if or else statement
(define M_state_if_else
  (lambda (condition full_expression statement1 statement2 state return break continue throw class this super)
    (cond
      ((boolean2 (M_value condition full_expression state throw class this super)) (M_state statement1 full_expression state return break continue throw class this super))
      (else (M_state statement2 full_expression state return break continue throw class this super)))))
                                            
;M_declare is a variable declaration, if no value is given, it will give the value of the variable as 'null x = 5
(define M_declare
  (lambda (declaration full_expression s throw class this super)
    (cond
      ((and (not (singleState? s))
            (or (eq? 'false (lookup (operand1 declaration) (getFirstLayer s) this super))
                (eq? 'true (lookup (operand1 declaration) (getFirstLayer s) this super))
                (number? (lookup (operand1 declaration) (getFirstLayer s) this super))))
       (error "variable already declared"))
      ((and (singleState? s)
            (or (eq? 'false (lookup (operand1 declaration) s this super))
                (eq? 'true (lookup (operand1 declaration) s this super))
                (number? (lookup (operand1 declaration) s this super))))
       (error "variable already declared"))
      ((not (null? (checkOperand2 declaration))) (M_insert (operand1 declaration) (M_value (operand2 declaration) full_expression s throw class this super) s))
      (else (M_insert (operand1 declaration) 'null s)))))

;M_assign assigns a variable with a value, the variable has to be declared
(define M_assign
  (lambda (assign full_expression state throw class this super)
    (cond
      ((null? state) state)
      ((and (not (list? (operand2 assign))) (or (eq? (M_value (operand2 assign) full_expression state throw class this super) 'undefined) (eq? (lookup (operand1 assign) state this super) 'undefined))) (error 'unknown "variable not declared"))
      ((not (list? (operand2 assign))) (begin (set-box! (M_lookup (operand1 assign) state this super) (M_value (operand2 assign) full_expression state throw class this super)) state))
      ((eq? (lookup (operand1 assign) state this super) 'undefined) (error "variable not declared"))
      ((eq? (operator (operand2 assign)) 'funcall)  (begin (set-box! (M_lookup (operand1 assign) state this super) (M_value (operand2 assign) full_expression state throw class this super)) state))
      ((eq? (M_value (operand2 assign) full_expression state throw class this super) 'undefined) (error "variable not declared"))
      (else (begin (set-box! (M_lookup (operand1 assign) state this super) (M_value (operand2 assign) full_expression state throw class this super)) state)))))

;M_insert inserts the variable and the value into the first layer of the state
(define M_insert
  (lambda (var value s)
    (cond
      ((singleState? s) (cons (cons var (getAllVar s)) (cons (cons (box value) (getAllValues s)) '())))
      (else (cons (M_insert var value (getFirstLayer s)) (otherLayers s))))))

;M_remove removes the variable and its value from the state
(define M_remove
  (lambda (var s)
    (cond
      ((null? s) s)
      ((singleState? s) (M_remove_single_state var s))
      ((inFirstLayer? var (getFirstLayer s)) (cons (M_remove_single_state var (getFirstLayer s)) (otherLayers s)))
      (else (cons (getFirstLayer s) (list (M_remove var (restOfLayers s))))))))

(define M_remove_single_state
  (lambda (var s)
    (cond
      ((null? s) s)
      ((eq? (getFirstVar s) var) (restOfState s))
      (else (M_insert (getFirstVar s) (getFirstValue s) (M_remove_single_state var (restOfState s)))))))

;M_lookup returns the box of the variable given from the state.
(define M_lookup
  (lambda (name state this super)
    (cond
      ((null? state) 'undefined)
      ((list? name) (M_dotlookup name state this super))
      ((singleState? state) (checkLayer name state))
      ((inFirstLayer? name (getFirstLayer state)) (checkLayer name (getFirstLayer state)))
      (else (M_lookup name (restOfLayers state) this super)))))

(define M_dotlookup
  (lambda (dotexpression state this super)
    (cond
      ((null? state) 'undefined)
      ((eq? (operand1 dotexpression) 'this) (M_lookup (operand2 dotexpression) this this super)) ;'this'
      ((eq? (operand1 dotexpression) 'super) (M_lookup (operand2 dotexpression) (restOfLayers this) this super))
      (else (M_lookup (operand2 dotexpression) (M_lookup (getClass (operand1 dotexpression) state this super) state this super) this super))))) ;'new' and variables

;lookup returns the value of the variable given from the state.
(define lookup
  (lambda (name state this super)
    (cond
      ((null? state) 'undefined)
      ((list? name) (dotlookup name state this super))
      ((singleState? state) (checkLayer-unbox name state))
      ((inFirstLayer? name (getFirstLayer state)) (checkLayer-unbox name (getFirstLayer state)))
      (else (lookup name (restOfLayers state) this super)))))

(define dotlookup
  (lambda (dotexpression state this super)
    (cond
      ((null? state) 'undefined)
      ((eq? (operand1 dotexpression) 'this) (lookup (operand2 dotexpression) this this super)) ;'this'
      ((eq? (operand1 dotexpression) 'super) (lookup (operand2 dotexpression) (restOfLayers this) this super)) ;super
      (else (lookup (operand2 dotexpression) (lookup (getClass (operand1 dotexpression) state this super) state this super) this super))))) ;'new' and variables
 

;abstractions

(define outerScope cadr)

(define className cadr)

(define funcName cadr)

(define getActualParams cddr)

(define currentThrow car)

(define restOfThrow cdr)

(define catch_finally_body cddr)

(define checkOperand2 cddr)

(define getAllValues cadr)

(define getAllVar car)

(define otherLayers cdr)

(define getFirstLayer car)

(define pop cadr)

(define type caar)

(define restOfExpression cdr)

(define restOfLayers cadr)

(define declareVar car)

(define currentExp car)

(define try_body cadr)

(define finally_body cadddr)

(define exception caadr)  

(define nextOperation cdr)

(define catch_body caddr)

(define catch_finally_body cddr)

(define operator car)

(define operand1 cadr)

(define operand2 caddr)

(define else cadddr)

(define funcName cadr)

(define restOfFunc cddr)

(define param car)

(define body cadr)

(define getFirstParam car)

(define restOfParams cdr)

;helper methods

;modifies the body so that 'return is changed to 'returnState 
(define modified_body
  (lambda (funcBody)
    (cond
      ((null? funcBody) '())
      ((list? (operator funcBody)) (cons (modified_body (currentExp funcBody)) (modified_body (restOfExpression funcBody))))
      ((eq? (operator funcBody) 'function) funcBody)
      ((eq? (operator funcBody) 'return) (cons 'returnState (restOfExpression funcBody)))
      (else (cons (currentExp funcBody) (modified_body (restOfExpression funcBody)))))))

;calls the function within its function environment and returns a value instead of a state
(define callFunc
  (lambda (name funcEnv full_expression throw class this super)
    (cond
      ((eq? 'this (operand1 name)) (interpretFunc (body (lookup name funcEnv this super)) funcEnv full_expression throw class this super))
      ((eq? 'super (operand1 name)) (interpretFunc (body (lookup name funcEnv this super)) funcEnv full_expression throw class this super))
      ((list? (operand1 name)) (interpretFunc (body (lookup name funcEnv this super)) funcEnv full_expression throw class (lookup (newClassName name) funcEnv this super) super)) ;looking up class name new A().f()
      (else (interpretFunc (body (lookup name funcEnv this super)) funcEnv full_expression throw class (lookup (operand1 name) funcEnv this super) super)))))

(define newClassName cadadr)

;get the formal parameters of the function given
(define getFormalParams
  (lambda (name state this super)
    (car (lookup name state this super))))

;called when it sees returnState -- changes the global variables of the state to return a state rather than a value
(define state_changer
  (lambda (getValue state)
    state))

;gets the function environment of the function when it is called that includes the initial/top-level state and its parameters 
(define getFuncEnv
  (lambda (actualParameters formalParameters state full_expression throw class this super)
    (cond
      ((not (eq? (length actualParameters) (length formalParameters))) (error "Mismatched Parameters"))
      ((null? actualParameters) (createFuncEnv state))
      (else (getFuncEnv (restOfParams actualParameters) (restOfParams formalParameters)
                    (M_insert (getFirstParam formalParameters) (M_value (getFirstParam actualParameters) full_expression (outerScope state) throw class this super) state)
                    full_expression throw class this super)))))

;creates the function environment from the state
(define createFuncEnv
  (lambda (state)
    (cons (getFirstLayer state) (cons (cons (getInitialState state) (cons (restOfLayers state) '())) '()))))

;gets the top-level state of our state
(define getInitialState
  (lambda (state)
    (cond
      ((singleState? state) state)
      ((singleState? (outerScope state)) (outerScope state))
      (else (getInitialState (outerScope state))))))

;inserts the function name and its closure into the top-level state
(define funcInsert
  (lambda (name closure env this super)
    (cond
      ((pair? (lookup name env this super)) (error "function already exists"))
      ((singleState? env) (cons (cons name (getAllVar env)) (cons (cons (box closure) (getAllValues env)) '())))
      (else (cons (cons (cons name (getAllVar (getFirstLayer env))) (cons (cons (box closure) (getAllValues (getFirstLayer env))) '())) (cons (restOfLayers env) '()))))))

;creates the function closure of the function that includes the parameters, body, and the empty state (for now)
(define funcClosure
  (lambda (function classname)
    (cons (param function) (cons (body function) (cons classname '())))))

(define funcClass caddr)

;adding new frame to state
(define push
  (lambda (state)
    (cons '(() ()) (list state))))

;checking if there is only one frame in the state
(define singleState?
  (lambda (state)
    (cond
      ((null? (cadr state)) #t)
      ((atom2? (caadr state)) #t)
      (else #f))))

;checking if element is in first layer of state
(define inFirstLayer?
  (lambda (name state)
    (cond
      ((null? (getAllVar state)) #f)
      ((eq? name (getFirstVar state)) #t)
      (else (inFirstLayer? name (restOfState state))))))

;checking if element is in the current layer of the state
(define checkLayer
  (lambda (name state)
    (cond
      ((null? (getAllVar state)) 'undefined)
      ((eq? name (getFirstVar state)) (getFirstValue state))
      (else (checkLayer name (restOfState state))))))

(define checkLayer-unbox
  (lambda (name state)
    (cond
      ((null? (getAllVar state)) 'undefined)
      ((eq? name (getFirstVar state)) (unbox (getFirstValue state)))
      (else (checkLayer-unbox name (restOfState state))))))

;returns the first variable in the state
(define getFirstVar
  (lambda (s)
        (caar s)))

;returns the first value in the state
(define getFirstValue
  (lambda (s)
        (caadr s)))

;returns the rest of the state
(define restOfState
  (lambda (s)
    (cons (cdar s) (cons (cdadr s) '()))))

;an atom is not null, not a list, and not an operator
(define atom?
  (lambda (x)
    (cond
      ((eq? '- x) #f)
      ((eq? '+ x) #f)
      ((eq? '* x) #f)
      ((eq? '/ x) #f)
      ((eq? '% x) #f)
      ((eq? '== x) #f)
      ((eq? '!= x) #f)
      ((eq? '>= x) #f)
      ((eq? '<= x) #f)
      ((eq? '> x) #f)
      ((eq? '< x) #f)
      ((eq? '! x) #f)
      ((eq? '|| x) #f)
      ((eq? '&& x) #f)
      ((eq? '= x) #f)
      ((or (eq? 'false x) (eq? 'true x)) #f) 
      (else (and (not (number? x)) (not (null? x)) (not (pair? x)))))))

;used for checking in singleState?
(define atom2?
  (lambda (x)
    (cond
      ((eq? '- x) #f)
      ((eq? '+ x) #f)
      ((eq? '* x) #f)
      ((eq? '/ x) #f)
      ((eq? '% x) #f)
      ((eq? '== x) #f)
      ((eq? '!= x) #f)
      ((eq? '>= x) #f)
      ((eq? '<= x) #f)
      ((eq? '> x) #f)
      ((eq? '< x) #f)
      ((eq? '! x) #f)
      ((eq? '|| x) #f)
      ((eq? '&& x) #f)
      ((eq? '= x) #f)
      ((box? x) #t)
      ((or (eq? 'false x) (eq? 'true x)) #t) 
      (else (and (not (null? x)) (not (pair? x)))))))

;ifelse? determines if it is an if else statement
(define ifelse?
  (lambda (expression)
    (if (pair? (cdddr expression))
        #t
        #f)))

;returns the string version of #t and #f
(define boolean
  (lambda (expression)
    (if expression
        'true
        'false)))

;returns the # version of true and false
(define boolean2
  (lambda (expression)
    (if (or (eq? 'true expression) (eq? #t expression))
        #t
        #f)))

(define myAnd
  (lambda (e1 e2)
    (cond
      ((and (eq? 'true e1) (eq? 'true e2)) #t)
      ((and (eq? #t e1) (eq? 'true e2)) #t)
      ((and (eq? 'true e1) (eq? #t e2)) #t)
      ((and (eq? #t e1) (eq? #t e2)) #t)
      (else #f))))
        
(define myOr
  (lambda (e1 e2)
    (cond
      ((and (eq? 'false e1) (eq? 'false e2)) #f)
      ((and (eq? #f e1) (eq? 'false e2)) #f)
      ((and (eq? 'false e1) (eq? #f e2)) #f)
      ((and (eq? #f e1) (eq? #f e2)) #f)
      (else #t))))

(define myNot
  (lambda (e)
    (cond
      ((eq? 'false e) #t)
      ((eq? #f e) #t)
      ((eq? 'true e) #f)
      ((eq? #t e ) #f))))