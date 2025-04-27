;; authors: rachel tjarksen
;;          damario hamilton
;;          jonathan da silva


#lang racket

(require "classParser.rkt")
(require "lex.rkt")


;; the state functions are the ones that end with "var" 
;; the m_state functions start with "eval"
;; and the m_value functions start with "eval-value"
;; the helper functions begin with "get"


;; here are the helper functions –––––––––––––––––––––––––––––––––
;; i used filter and assoc here in order to help with abstraction


;; get the value of the variable being returned
(define (get-inside-brackets expr) (cdr expr))

;; get the operand for math
(define (get-operand expr) (car expr))

;; get the left term in binary math
(define (get-left-term expr) (cadr expr))

;; get the inside of a parenthetical
(define (get-inside expr) (car expr))

;; get the right term in binary math
(define (get-right-term expr) (caddr expr))

;; get the condition for an if statement
(define (get-condition expr) (cadr expr))

;; get the true branch for an if statement
(define (get-true-branch expr) (caddr expr))

;; get the false branch for an if statement
(define (get-false-branch expr)
  (if (> (length expr) 3)
      (cadddr expr)
      '()))

;; get the body for a while loop
(define (get-body expr) (caddr expr))

;; get the control flow word
(define (get-flow expr) (car expr))

;; get the variable for assingment
(define (get-var expr) (cadr expr))

;; get the value for assingment
(define (get-value expr) (caddr expr))

;; get the statement being returned
(define (get-return-stmt expr) (cadr expr))

;; get the try block in a try-catch
(define (get-try-block expr) (cadr expr))

;; get the catch block in a try-catch
(define (get-catch-block expr)
  (if (not (null? (caddr expr)))
      (caddr (caddr expr))
      '()))

;; get the error variable name in a try-catch
(define (get-catch-var expr)
  (if (not (null? (caddr expr)))
      (car (cadr (caddr expr)))
      '()))

;; get the error that is being thrown
(define (get-error expr) (cadr expr))

;; get the finally block in a try-catch
(define (get-finally-block expr)
  (if (not (null? (cadddr expr)))
      (cadr (cadddr expr))
      '()))

;; get the possible error in a return value
(define (get-possible-error expr)
  (car expr))

;; get the possible state in a return value
(define (get-possible-state expr) (cadr expr))

;; get the function name from a function definition
(define (get-func-name expr) (cadr expr))

;; get the parameters for a function
(define (get-params expr) (caddr expr))

;; get the function body
(define (get-func-body expr) (cadddr expr))

;; get the global frame from the state
(define (get-global-frame expr) (car expr))

;; get the class frame from the state
(define (get-class-frame expr) (cadr expr))

;; get the local (top) frame from the call stack
(define (get-local-frame expr) (caddr expr))

;; get the previous frame (the rest of the call stack)
(define (get-prev-frame expr) (cadddr expr))

;; get the body of a function call expression
(define (get-funcall-body expr) (cadr expr))

;; extract the value from a lookup result
(define (get-lookup-value expr) (car expr))

;; extract the location ('g or 'l) from a lookup result
(define (get-location expr) (cadr expr))

;; get the return value from a function
(define (get-return-value expr) (car expr))

(define (get-class-name expr) (cadr expr))

(define (get-extends expr) (caddr expr))

(define (get-class-body expr) (cadddr expr))




;; here are the state functions –––––––––––––––––––––––––––––––––


;; lookup a variable in the state
(define lookup-helper
  (lambda (var frame)
    (cond
      ((null? frame) #f)
      ;; if the structure is a pair and the first element is the variable, return the rest of the list
      ((and (pair? frame) (symbol? (car frame)))
       (if (eq? (car frame) var)
           (if (eq? (cdr frame) #f)
               'false
               (cdr frame))
          #f))
      ;; if the structure is a pair or list, recursively search
      ((pair? frame)
       (or (lookup-helper var (car frame))
           (lookup-helper var (cdr frame))))
      ;; not found
      (else #f))))



;; main function to look up a variable in the state
(define lookup-var
  (lambda (var state)
    (cond
      ((let ((v (lookup-helper var (get-local-frame state))))
         (if v (list v 'l) #f)))
      ((let ((v (lookup-helper var (get-class-frame state))))
         (if v (list v 'c) #f)))
      ((let ((v (lookup-helper var (get-global-frame state))))
         (if v (list v 'g) #f)))
      (else #f))))



;; tells us if a var exists or not (duh)
(define var-exists?
  (lambda (var state)
    (if (not (lookup-var var state))
        #f
        #t)))



;; function to declare a variable
(define declare-var
  (lambda (var value state)
    (let ((real-state (get-local-frame state)))
      (if (eq? var 'return)  ;; special case for 'return' variable
          (list (append (get-global-frame state) (list (cons var value))) (get-class-frame state) (get-local-frame state) (get-prev-frame state))
          (if (or (null? real-state) (pair? (car real-state)))
              (list (get-global-frame state) (get-class-frame state) (cons (cons var value) real-state) (get-prev-frame state))  ;; create first layer with var
              (let* ((top-layer (car real-state)))
                (if (assoc var top-layer)  ;; already declared?
                    (error "variable already declared in this scope!" var)
                    (list (get-global-frame state) (get-class-frame state) (cons (cons (cons var value) top-layer) (cdr real-state)) (get-prev-frame state)))))))))



;; declare all variables in a parameter - value pair of lists
(define declare-all-vars
  (lambda (values params state break cont throw)
    (if (not (= (length values) (length params)))
        (error "mismatch between number of values and parameters!")
        (if (null? params)
            state
            (let* ((param (car params))
                   (value (eval-value-expr (car values) state break cont throw))
                   (new-state (declare-var param value state)))
              (declare-all-vars (cdr values) (cdr params) new-state break cont throw))))))




;; evaluate the parameters (yay)
(define eval-parameters
  (lambda (params state break cont throw)
    (map (lambda (param) (eval-value-expr param state break cont throw)) params)))



(define replace-inst-var
  (lambda (var new-val frame)
    (cond
      ;; base case: empty frame returns empty list
      ((null? frame) '())
      ;; we might have either an atomic key or a nested structure
      ((symbol? (car frame))
       (let* ((key (car frame)))
         (if (eq? key (cadr var))
             (replace-var (caddr var) new-val (cdr frame))
             frame)))
      ;; if the first lement is not a pair, recurse on it
      (else (cons (replace-inst-var var new-val (car frame))
                  (replace-inst-var var new-val (cdr frame)))))))
    



; helper to update key-value pair in a flat list of bindings
(define replace-var
  (lambda (var new-val frame)
    (if (not (lookup-helper var frame))
        frame
        (cond
          ;; base case: empty frame returns empty list
          ((null? frame) '())
          ;; we might have either an atomic key or a nested structure
          ((symbol? (car frame))
           (let* ((key (car frame)))
             (if (eq? key var)
                 (cons key new-val)
                 frame)))
          ;; if the first lement is not a pair, recurse on it
          (else (cons (replace-var var new-val (car frame))
                      (replace-var var new-val (cdr frame))))))))



;; main function to update var and return full state
(define update
  (lambda (var new-val state)
    (let ((result (if (list? var)
               (list (lookup-helper (caddr var) (get-class-frame state)) 'c)
               (lookup-var var state)))
          (new-var (if (list? var)
               (caddr var)
               var)))
      (displayln (replace-var new-var new-val (lookup-helper (cadr var) (get-local-frame state))))
      (displayln (get-local-frame state))
      (cond
        ;; update an object
        ((list? var)
         (list
          (get-global-frame state)
          (get-class-frame state)
          (replace-inst-var var new-val (get-local-frame state))
          (get-prev-frame state)))
        ;; update global frame
        ((and result (equal? (get-location result) 'g))
         (list
          (replace-var new-var new-val (get-global-frame state))
          (get-class-frame state)
          (get-local-frame state)
          (get-prev-frame state)))
        ;; update class frame
        ((and result (equal? (get-location result) 'c))
         (list
          (get-global-frame state)
          (replace-var new-var new-val (get-class-frame state))
          (get-local-frame state)
          (get-prev-frame state)))
        ;; update local frame
        ((and result (equal? (get-location result) 'l))
         (list
          (get-global-frame state)
          (get-class-frame state)
          (replace-var new-var new-val (get-local-frame state))
          (get-prev-frame state)))
        (else (error "variable not found!" new-var))))))



;; add a layer to the current state!
(define add-layer
  (lambda (state)
    (let ((real-state (get-local-frame state)))
      (list (get-global-frame state) (cons '() real-state) (get-prev-frame state)))))



;; get rid of irrelevant variables in the SCOPE not the frame
(define destroy-scope
  (lambda (state)
    (let ((real-state (get-local-frame state)))
      (list (get-global-frame state) (cdr real-state) (get-prev-frame state)))))



;; helper function to remove a bariable from the state
(define remove-helper
  (lambda (var frame)
    (if (not (lookup-helper var frame))
        frame
        (cond
          ;; base case: empty frame returns empty list
          ((null? frame) '())
          ;; we might have either an atomic key or a nested structure
          ((symbol? (car frame))
           (let* ((key (car frame))
                  (val (cdr frame)))
             (if (eq? key var)
                 '()
                 (cons frame (remove-helper var (cdr frame))))))
          ;; recurse!
          (else (cons (remove-helper var (car frame))
                      (remove-helper var (cdr frame))))))))



;; remove a variable (most always return)
(define remove-var
  (lambda (var state)
    (list (remove-helper var (get-global-frame state)) (get-class-frame state) (get-local-frame state) (get-prev-frame state))))





;; here are the m_value functions–––––––––––––––––––––––––––––––––


;; evaluate a mathematical expression
(define eval-value-math
  (lambda (expr state break cont throw)

    (cond
      ;;  check if the expr is a symbol and not declared (undefined)
      ((symbol? expr)
       (let ((value (get-lookup-value (lookup-var expr state))))
         (if (eq? value 'undefined)
             (error "variable not declared! can't do any math on it")
             value)))

      ;; literal numbers: return the number itself!
      ((number? expr)
       expr)

      ;; math time!
      ((and (list? expr)
            (let ((operand (get-operand expr)))
              (or (eq? operand '+)
                  (eq? operand '-)
                  (eq? operand '*)
                  (eq? operand '/)
                  (eq? operand '%))))
       
       (if (= (length expr) 2)  ;; check if it's unary or binary

           ;; unary negation case (- (expr))
           (if (eq? (get-operand expr) '-)
               (- (eval-value-expr (get-left-term expr) state))
               (error "unknown operation"))

           ;; binary math case (+ left right, etc.)
           (let ((left (eval-value-expr (get-left-term expr) state break cont throw))
                 (right (eval-value-expr (get-right-term expr) state break cont throw))
                 (operand (get-operand expr)))
             (case operand
               ((+) (+ left right))
               ((-) (- left right))
               ((*) (* left right))
               ((/) (quotient left right))
               ((%) (modulo left right))))))

      ;; parenthesized expressions
      ((and (list? expr) (= (length expr) 1))
       (eval-value-math (get-inside expr) state))

      ;; error case: unknown expression
      (else (error "unknown expression" expr)))))



;; evaluate comparison expressions (=, <, >, <=, >=)
(define eval-value-comparison
  (lambda (expr state break cont throw)
    (let ((left (eval-value-expr (get-left-term expr) state break cont throw))
          (right (eval-value-expr (get-right-term expr) state break cont throw))
          (operand (get-operand expr)))
      (cond
        ((eq? operand '==) (= left right))
        ((eq? operand '!=) (not (= left right)))
        ((eq? operand '<) (< left right))
        ((eq? operand '>) (> left right))
        ((eq? operand '<=) (<= left right))
        ((eq? operand '>=) (>= left right))
        (else (error "unknown comparison operator" operand))))))



;; evaluate logical negation (not)
(define eval-value-not
  (lambda (expr state)
    (not (eval-value-expr (get-left-term expr) state))))



;; evaluate logical "and"
(define eval-value-and
  (lambda (expr state break cont throw)
    (let ((left (eval-value-expr (get-left-term expr) state break cont throw))
          (right (eval-value-expr (get-right-term expr) state break cont throw)))
      (and left right))))



;; evaluate logical "or"
(define eval-value-or
  (lambda (expr state break cont throw)
    (let ((left (eval-value-expr (get-left-term expr) state break cont throw))
          (right (eval-value-expr (get-right-term expr) state break cont throw)))
      (or left right))))



;; evaluate an expression
(define eval-value-expr
  (lambda (expr state break cont throw)
    (cond
      ;; numbers and true/false
      ((number? expr) expr)
      ((equal? expr #t) #t)
      ((equal? expr #f) #f)

      ;; true and false symbols: convert to #t and #f
      ((eq? expr 'true) #t)
      ((eq? expr 'false) #f)

      ;; look up the variable in the state, error if not found
      ((symbol? expr)
       (let ((value (lookup-var expr state)))
         (cond
           ((eq? value #f) (error "variable not defined!" expr))
           ((eq? (car value) 'undefined) (error "this variable is not defined but not declared!" expr))
           ((eq? (car value) 'false) #f)
           (else (car value)))))

     ;; math expressions (addition, subtraction, etc.)
      ((let ((operand (get-operand expr)))
         (or (eq? operand '+)
             (eq? operand '-)
             (eq? operand '*)
             (eq? operand '/)
             (eq? operand '%)))
       (eval-value-math expr state break cont throw))

      ;; comparison expressions (=, <, >, <=, >=)
      ((let ((operand (get-operand expr)))
         (or (eq? operand '==)
             (eq? operand '!=)
             (eq? operand '<)
             (eq? operand '> )
             (eq? operand '<=)
             (eq? operand '>=)))
       (eval-value-comparison expr state break cont throw))

      ;; logical negation (not)
      ((eq? (get-operand expr) '!) 
       (not (eval-value-expr (get-left-term expr) state break cont throw)))

      ;; logical and
      ((eq? (get-operand expr) '&&)
       (eval-value-and expr state break cont throw))

      ;; logical or
      ((eq? (get-operand expr) '||)
       (eval-value-or expr state break cont throw))

      ;; new object
      ((eq? (get-operand expr) 'new)
       (get-local-frame (eval-sequence (get-lookup-value (lookup-var (cadr expr) state)) '(() () () ()) break cont throw)))

      ((eq? (get-operand expr) 'dot)
       (if (eq? (cadr expr) 'this)
           (lookup-helper (caddr expr) (get-class-frame state))
           (lookup-helper (caddr expr) (get-lookup-value (lookup-var (cadr expr) state)))))

      ;; when a function evaluates to a number
      ((eq? (get-operand expr) 'funcall)
       (get-return-value (eval-func expr state break cont throw)))

      ;; other expressions (error)
      (else expr)))) ;; todo: needs unknown expression idk





;; here are the m_state functions –––––––––––––––––––––––––––––––––


;; evalaute a block function, like the one with brackets
(define eval-block
  (lambda (stmt state break cont throw)
    (let* ((block-content (get-inside-brackets stmt)))  ;; extract the block content
      (let ((result
             (eval-sequence block-content (add-layer state) break cont throw)))
      (destroy-scope result)))))



;; evaluate an entire try-block with try/catch/finally
(define eval-whole-try-block
  (lambda (stmt state break cont throw)
    (destroy-scope (eval-try-catch stmt state break cont throw))))



;; evaluate an if statement
(define eval-if
  (lambda (stmt state break cont throw)
    (let* ((condition (get-condition stmt))  ;; get the condition part
           (true-branch (get-true-branch stmt))  ;; get the true branch
           (false-branch (get-false-branch stmt))  ;; get the false branch
           (condition-value (eval-value-expr condition state break cont throw))) ;; evaluate condition to true or false
      (if condition-value
          (eval-stmt true-branch state break cont throw)  ;; execute true branch if condition is true
          (if (not (null? false-branch))
              (eval-stmt false-branch state break cont throw)  ;; execute false branch if it exists
              state))))) ;; otherwise, unchanged state



;; evaluate the 'while' loop
(define eval-while
  (lambda (stmt state break cont throw)
    (let* ((condition (get-condition stmt))   ;; <cond>
           (body (get-body stmt))             ;; <body>
           (condition-value (eval-value-expr condition state break cont throw)))  ;; evaluate condition
      (if condition-value
          (let ((new-state (call/cc
                            (lambda (cont-exit)
                              (eval-stmt body state break cont-exit throw)))))
            (eval-while stmt new-state break cont throw))
          state))))




;; evaluate a try catch block
(define eval-try-catch
  (lambda (stmt state break cont throw)
    (let* ((try-block (get-try-block stmt))
           (catch-block (get-catch-block stmt))
           (catch-var (get-catch-var stmt))
           (finally-block (get-finally-block stmt))
           (result (eval-try try-block (add-layer state) break cont throw)))
      
      (let* ((new-state (if (pair? (get-possible-error result))
                            result                 ;; return value is just the state
                            (get-possible-state result)))         ;; need to extract state from return value
             (error-code (if (pair? (get-possible-error result))
                             '()                   ;; no error code (no catch)
                             (get-possible-error result)))        ;; there is an error code
             (catch-state (if (null? error-code)
                              new-state
                              (eval-sequence catch-block 
                                             (declare-var catch-var error-code new-state) 
                                             break cont throw)))
             (final-state (if (null? finally-block)
                              catch-state
                              (eval-sequence finally-block catch-state break cont throw))))
        final-state))))



;; evaluates a 'try' block using call/cc
(define eval-try
  (lambda (try-block state break cont throw)
    (let ((result
            (call/cc
             (lambda (throw-error)
               (eval-sequence try-block state break cont throw-error)))))
      result)))




;; evaluate a function call
(define eval-func
  (lambda (stmt state break cont throw)
    (let* ((name         (get-func-name stmt))
           (args         (if (> (length stmt) 2)
                             (eval-parameters (cddr stmt) state break cont throw)
                             '()))
           (func-and-loc (if (list? name)
                             (list (eval-value-expr name state break cont throw) 'c)
                             (lookup-var name state)))
           (func         (car func-and-loc))
           (loc          (get-location func-and-loc))  ;; assume 'g for global, otherwise local
           (params       (car func))
           (body         (get-funcall-body func))
           (new-state    (cond
                           ((equal? loc 'g)
                            (declare-all-vars args params
                                              (list (get-global-frame state) (get-class-frame state) '() (cons (get-local-frame state) (get-prev-frame state)))
                                              break cont throw))
                           ((equal? loc 'c)
                            (if (list? name)
                                (declare-all-vars args params
                                                  (list (get-global-frame state) (get-lookup-value (lookup-var (cadr name) state)) '() (list (get-class-frame state) (get-local-frame state) (get-prev-frame state)))
                                                  break cont throw)
                                (declare-all-vars args params
                                                  (list (get-global-frame state) (get-class-frame state) (get-local-frame state) (get-prev-frame state))
                                                  break cont throw)))
                             (declare-all-vars args params 
                                               (list (cons (get-local-frame state) (get-global-frame state)) (get-class-frame state) '() (get-prev-frame state))
                                               break cont throw))))
      (call/cc
       (lambda (throw-error)
         ;; wrap the throw continuation to perform cleanup before escaping
         (let ((wrapped-throw
                (lambda (value)
                  ;; do the appropriate frame cleanup before propagating the throw!
                  (let ((cleaned-state (if (equal? loc 'g)
                                           (cleanup-global new-state)
                                           (cleanup-local new-state))))
                    (throw (list (car value) (remove-var 'return cleaned-state)))))))
           (let* ((result (eval-sequence body new-state break cont wrapped-throw))
                  (ret-val (lookup-var 'return result))
                  (value (if ret-val
                             (car ret-val)
                             #f)))
             ;; normal return
             (cond
               ((equal? loc 'g)
                 (list value (cleanup-global (remove-var 'return result))))
               ((equal? loc 'c)
                (list value (cleanup-class (remove-var 'return result) name)))
               (else
                 (list value (cleanup-local (remove-var 'return result))))))))))))




;; cleaning up the frame in the case of a global state
(define cleanup-global
  (lambda (state)
    (list (get-global-frame state) (get-class-frame state) (car (get-prev-frame state)) (cdr (get-prev-frame state)))))



;; cleaning up the frame in the case of a class state
(define cleanup-class
  (lambda (state name)
    (if (list? name)
        (list (get-global-frame state) (car (get-prev-frame state)) (list (cons (cadr name) (get-class-frame state)) (cadr (get-prev-frame state))) (caddr (get-prev-frame state))) 
        (list (get-global-frame state) (get-class-frame state) (get-local-frame state) (get-prev-frame state)))))



;; cleaning up the frame in the case of a local state
(define cleanup-local
  (lambda (state)
    (list (cdr (get-global-frame state)) (get-class-frame state) (car (get-global-frame state)) (get-prev-frame state))))



;; evaluate the return of a function
(define eval-return
  (lambda (stmt state break cont throw)
    (let* ((value 
            (if (and (list? stmt) (eq? (get-flow stmt) 'funcall))
                (get-return-value (eval-func stmt state break cont throw))
                (let ((val (eval-value-expr stmt state break cont throw)))
                  (cond
                    ((eq? val #f) 'false)
                    ((eq? val #t) 'true)
                    (else val))))))
      value)))



;; add a function declaration to the state + environment
(define eval-function-declaration
  (lambda (stmt state break cont throw)
    (let ((name (get-func-name stmt))
          (params (get-params stmt))
          (body (get-func-body stmt)))
      (if (var-exists? name state)  ;; check if the function already exists in the environment
          (error "function already defined!" name)
          ;; create the closure and add it to the environment
          (let ((closure (list params body)))
            (declare-var name closure state))))))



(define eval-class-declaration
  (lambda (stmt state break cont throw)
    (let ((name (get-class-name stmt))
          (extends (get-extends stmt))
          (body (get-class-body stmt)))
      (declare-var name body state))))
      

  

;; evaluate a statement (this is the main function)
(define eval-stmt
  (lambda (stmt state break cont throw)

    (let ((control-flow (get-flow stmt)))  ;; use get-flow to determine the flow type
      (cond
        ;; base case: empty statement list
        ((null? stmt) state)

        ;; handle 'function' statements
        ((eq? control-flow 'function)
         (eval-function-declaration stmt state break cont throw))

        ;; handle 'static-function' statements todo: make it NORMAL
        ((eq? control-flow 'static-function)
         (eval-function-declaration stmt state break cont throw))

        ;; handle user-defined function calls
        ((eq? control-flow 'funcall)
         (eval-func stmt state break cont throw))

        ;; handle class declarations
        ((eq? control-flow 'class)
         (eval-class-declaration stmt state break cont throw))

        ;; handle 'var' declaration
        ((eq? control-flow 'var)
         (if (= (length stmt) 2)
             (declare-var (get-var stmt) 'undefined state)
             (declare-var (get-var stmt) (eval-value-expr (get-value stmt) state break cont throw) state)))

        ;; handle 'return' statement
        ((eq? control-flow 'return)
         (let ((ret-val (eval-return (get-return-stmt stmt) state break cont throw)))
           ;; do nothing if 'return' already exists in the state
           (if (not (var-exists? 'return state))
               (declare-var 'return ret-val state)
               state)))

        ;; handle 'if' statements
        ((eq? control-flow 'if)
         (eval-if stmt state break cont throw))

        ;; handle assignment (=) statement
        ((eq? control-flow '=)
         (update (get-var stmt) (eval-value-expr (get-value stmt) state break cont throw) state))
        
        ;; handle 'while' loop statement
        ((eq? control-flow 'while)
         (call/cc
          (lambda (break-exit)  ;; named exit continuation for debugging!
            (eval-while stmt state break-exit cont throw)))) ;; todo: get rid of garbage after call/cc

        ;; handle 'break' statement
        ((eq? control-flow 'break)
         (break state))

        ;; handle 'continue' statement
        ((eq? control-flow 'continue)
         (cont state))

        ;; handle 'try' statement
        ((eq? control-flow 'try)
         (eval-whole-try-block stmt state break cont throw))

        ;; handle 'throw' statement
        ((eq? control-flow 'throw)
         (throw (list (eval-value-expr (get-error stmt) state break cont throw) state)))

        ;; handle block (begin) statements (e.g., { ... })
        ((eq? control-flow 'begin)
         (eval-block stmt state break cont throw))

        ;; handle sequences of statements (nested lists)
        ((list? stmt) 
         (eval-sequence stmt state break cont throw))

        ;; handle unknown statements
        (else (error "unknown statement" stmt))))))



;; evaluate nested statements!
;; i did not use helpers for car and cdr here, because they literally represent "the first statement" and "everything else"
;; it would not be helpful in this case
(define eval-sequence
  (lambda (stmts state break cont throw)
    (cond
      ((null? stmts) state)
      (else
       (let ((new-state (eval-stmt (car stmts) state break cont throw)))
         (if (or (number? (car new-state)) (not (car new-state)))
             (eval-sequence (cdr stmts) (cadr new-state) break cont throw)
             (eval-sequence (cdr stmts) new-state break cont throw)))))))



; run the main function
(define run-main
  (lambda (state)
    (let ((new-state (list (get-global-frame state) (get-local-frame state) '() '()))
          (call (list 'funcall 'main)))
      (get-return-value (eval-func call new-state
                      (lambda (new-state) (error "you can't use 'break' just anywhere!") new-state)
                      (lambda (new-state) (error "you can't use 'continue' just anywhere!") new-state)
                      (lambda (new-state) (error "you can't use 'throw' just anywhere!") new-state))))))



(define run-class
  (lambda (state classname)
    (let ((class-body (get-lookup-value (lookup-var classname state)))
          (new-state (list (get-local-frame state) '() '() '())))
      (run-main (eval-sequence class-body new-state
                      (lambda (new-state) (error "you can't use 'break' just anywhere!") new-state)
                         (lambda (new-state) (error "you can't use 'continue' just anywhere!") new-state)
                         (lambda (new-state) (error "you can't use 'throw' just anywhere!") new-state))))))


;; interpret ofc
(provide interpret)
(provide parser)
(define interpret
  (lambda (code classname)
    (run-class (eval-sequence code '(()()()())
                         (lambda (state) (error "you can't use 'break' just anywhere!") state)
                         (lambda (state) (error "you can't use 'continue' just anywhere!") state)
                         (lambda (state) (error "you can't use 'throw' just anywhere!") state)) classname)))


; change this to the name of your .txt file!
(interpret (parser "test/test5A.txt") 'A)






