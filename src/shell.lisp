;;;; COMP456
;;;; A simple shell for parsing an expert shell Lisp grammar

;;;; The following symbols represent built-in functions
;;;;
;;;; defact, defrule, reset, run, lisp
;;;;
;;;; and the following predicate functions
;;;;
;;;; ?is, ?and, ?or, ??, and ?~
;;;;

;;;; Global variable declarations
(defstruct fact
  rule-applied
  bindings
  (current nil)
  prev)

(defstruct prod-rule
  name
  rule
  action)

;;; Pattern matching hashtables
(setq *functions* (make-hash-table))
(setq *facts* (make-hash-table :test #'equal))
(setq *bindings* (make-hash-table :test #'equal))
(setq *rules* (make-hash-table :test #'equal))

;;; Functions match mappings
(setf (gethash 'load-ops *functions*) 'load-ops-fn)
(setf (gethash 'assert *functions*) 'assert-fn)
(setf (gethash 'defrule *functions*) 'defrule-fn)
(setf (gethash 'reset *functions*) 'reset-fn)
(setf (gethash 'quit *functions*) 'quit-fn)
(setf (gethash 'run *functions*) 'run-fn)
(setf (gethash 'show-rules *functions*) 'show-rules-fn)
(setf (gethash 'lisp *functions*) 'lisp-fn)
(setf (gethash '?if *functions*) 'if-fn)
(setf (gethash '?and *functions*) 'and-fn)
(setf (gethash '?or *functions*) 'or-fn)
(setf (gethash '?? *functions*) 'any-fn)
(setf (gethash '?~ *functions*) 'not-fn)
(setf (gethash '?= *functions*) 'equal-fn)
;;;
;;; Global variables
(setq index 0)
(setq *quit* nil)

;;;; Functions
;;; Not-Mapped functions

;;; bind-fact function binds a key-value pair to an existing
;;; fact in the *bindings* list, or creates a new pair if
;;; the binding does not exist
(defun bind (pair)
  (setf (gethash (first pair) *bindings*) (second pair)))

(defun get-binding (pair)
  (gethash (first pair) *bindings*))

(defun find-current ()
  (let ((ret nil))
    (maphash
     #'(lambda (key value)
		 (if (fact-current value)
		     (setf ret key)
		     nil))
	     *facts*)
  ret))

;;; eq-bindingp function determines whether two binding
;;; sets contain the same bindings.
;;; Returns t if binding sets are equal, nil if they are not
(defun eq-bindingp (b1 b2)
  (let ((ret t))
    (maphash #'(lambda (k v)
		 (if (not (eq (gethash k b2) v))
		     (setf ret nil)))
	     b1)
    ret))

;;; find-fact searchs the *facts* queue for a previous fact.
;;; This prevents a cycle where the *facts* queue represents
;;; the closed list in a DFS search algorithm.
;;; The function returns t if binding is found, otherwise nil.
(defun find-factp (bindings)
  (let ((ret nil))
    (maphash #'(lambda (k v)
		 (if (eq-bindingp (fact-bindings v) bindings)
		     (setf ret t)))
	     *facts*)
    ret))

;;; get-fact function retrieves a fact from the *facts*
;;; list
(defun get-fact (key)
  (gethash key *facts*))

;;; insert-fact function to insert a fact in the *facts*
;;; list
(defun insert-fact (bindings rule)
  (if (not (find-factp bindings))
      (let* ((prev (find-current))
	     (fact (make-fact :rule-applied rule
			      :bindings bindings
			      :current t
			      :prev prev)))
	(if prev (setf (fact-current (gethash prev *facts*)) nil))
	(setf (gethash (gen-fact-key) *facts*) fact))
      nil))
  
;;; copy-hash-table function
(defun copy-hash-table (ht)
  (let ((new-table (make-hash-table
                    :test (hash-table-test ht)
                    :size (hash-table-size ht))))
    (maphash #'(lambda(key value)
                 (setf (gethash key new-table) value))
             ht)
    new-table))

;;; gen-fact-key function generates a unique key symbol that is
;;; searchable in a hashtable.
(setq *fact-key-counter* 1000)
(defun gen-fact-key ()
  (let ((key (make-symbol (concatenate 'string "K"
			  (format nil "~a" *fact-key-counter*)))))
    (setf *fact-key-counter* (1+ *fact-key-counter*))
    key))

;;; gen-rule key function generates a unique key symbol for a rule
;;; and is searchable in a hashtable.
(setq *rule-key-counter* 2000)
(defun gen-rule-key ()
  (let ((key (make-symbol (concatenate 'string "R"
				       (format nil "~a" *rule-key-counter*)))))
    (setf *rule-key-counter* (1+ *rule-key-counter*))
    key))


;;; Mapped functions
(defun lisp-fn (arg)
  (if (listp (first arg))
      (eval (first arg))
      (eval arg)))

;;; assert function creates a fact and places it on the fact
;;; list if a template exists, inlcuding listed variable bindings
;;; in the *bindings* list.  Otherwise, it creates a value to
;;; variable binding only and places it on the *bindings* list.
;;;
;;; Example:
;;;
;;; Template assert
;;; S-SHELL> (assert <template> (<slot1>) (<slot2>))
;;;
;;; Variable direct bindings
;;; S_SHELL> (assert variable value)
;;;
(defun assert-fn (expr)
  (let ((f (first expr)))
  (cond ((atom f)
	 (setf (gethash f *bindings*) (second expr)))
	(t (match expr)))))

;;; show-rules-fn function
;;; Prints out the rules that reached the final state and returns a halt
;;; symbol to halt the inference engine.
(defun show-rules-fn ()
  (format t "Rules path:~%")
  (let* ((path nil)
	 (curr (find-current))
	 (prev (fact-prev (get-fact curr))))
    (loop while prev do
	 (push (fact-rule-applied (get-fact curr)) path)
	 (setf curr prev)
	 (setf prev (fact-prev (get-fact curr))))
    (format t "~{~a~%~}" (reverse path)))
  (format t "Final variable bindings:~%~a~%" *bindings*)
  'halt)

;;; if-fn function
;;; This function provides an if-then-else switch in an assert statement
(defun if-fn (expr)
;  (format t "if-fn: expr= ~a~%" expr)
  (let* ((predicate (first expr))
	 (then (second expr))
	 (else (third expr)))
;    (format t "predicate= ~a~%then= ~a~%else= ~a~%" predicate then else)
    (if (match predicate)
	(match then)
	(if else (match else)))))
  
;;; defrule function to define a production rule
;;;
;;; Example format: (defrule name (fact1 fact2 (rule1 fact3))
;;;
;;; The rule is a mix of fact assertions and other rules.
;;;
;;; Example:
;;;
;;; (defrule rule-equal
;;;     ; Production rule form
;;;     (?and arg1 arg2)
;;;     ; Action form
;;;     (assert (farmer east))
;;;
;;; The production rule is the conjunction (AND) of arg1 and arg2.
;;; This will fire the action located in the action form.  The action
;;; can only be a single assert, either a variable binding, or a templated
;;; fact.
(defun defrule-fn (expr)
  (let* ((name (first expr))
	 (rule (second expr))
	 (action (third expr))
	 (p-rule (make-prod-rule)))
    (setf (prod-rule-name p-rule) name)
    (setf (prod-rule-rule p-rule) rule)
    (setf (prod-rule-action p-rule) action)
    (setf (gethash name *rules*) p-rule)))
	
;;; reset function clears the working memory, facts and
;;; variable bindings, but keeps defined templates and
;;; rules
(defun reset-fn ()
  (clrhash *facts*)
  (clrhash *bindings*))

;;; run function runs the production rule inference engine
;;; until working memory is clear.
(defun run-fn ()
  (let ((run t))
    (loop while run do
	 (maphash
	  #'(lambda (key p-rule)
	      (if (match (get-rule key))
		  (progn
		    (let* ((*org-bindings* (copy-hash-table *bindings*))
			   (result (match (get-action key))))
		      ;; If binding found previous, do no apply
		      ;; to bindings.  This prevents cycles.
		      (if (find-factp *bindings*)
			  (setf *bindings* *org-bindings*)
			  (insert-fact (copy-hash-table *bindings*) key))
		      (if (equal result 'halt)
			  (return))))))		    
	  *rules*))))
	  
;;; and-fn (?and) function compares two variable bindings
(defun and-fn (expr)
  (let* ((arg1 (if (atom (first expr))
		   (first expr)
		   (match (first expr))))
	 (arg2 (if (atom (second expr))
		   (second expr)
		   (match (second expr)))))
    (and arg1 arg2)))

;;; or-fn (?or) function compares two variable bindings
;;; and return t or nil.
(defun or-fn (expr)
  (let* ((arg1 (if (atom (first expr))
		   (first expr)
		   (match expr)))
	 (arg2 (if (atom (second expr))
		   (second expr)
		   (match expr))))
    (or arg1 arg2)))

;;; any-fn (??) function matches anything.  This is just
;;; syntactic sugar, as the function always returns true.
(defun any-fn ()
  return t)

;;; not-fn (?~) function returns t if arg is nil, and nil
;;; if arg is not nil
(defun not-fn (expr)
;  (format t "not-fn expr= ~a, first=~a~%" expr (first expr))
  (if (atom (first expr))
      (process-tuple (first expr)
		     nil
		     #'(lambda (a b)
			 (if a
			     nil
			     t)))      
      (if (match (first expr))
	  nil
	  t)))
  
;;; equal-fn (?=) function determines in two variable bindings
;;; have the same value.
(defun equal-fn (expr)
  (let* ((arg1 (if (atom (first expr))
		   (first expr)
		   (match expr)))
	 (arg2 (if (atom (second expr))
		   (second expr)
		   (match expr))))
    (process-tuple arg1 arg2 #'(lambda (a b)
				 (equal a b)))))

;;; exit-fn function sets the REPL *exit* loop variable
(defun quit-fn ()
  (setf *quit* t))

;;; get-rule function gets rule from the name key in
;;; in the *rules* hashtable.
(defun get-rule (name)
  (let ((rule (gethash name *rules*)))
	(if rule (prod-rule-rule rule) nil)))

;;; get-assert function gets the action from the name key in
;;; the *rules* hashtable
(defun get-action (name)
  (let ((rule (gethash name *rules*)))
	(if rule (prod-rule-action rule) nil)))

;;; process-tuple function is a generic function that
;;; processes two arguments and a lambda comparison.
(defun process-tuple (arg1 arg2 fn)  
  (let ((a1 nil)
	(a2 nil))
    (if (atom arg1)
	(setf a1 (gethash arg1 *bindings*))
	(setf a1 (match arg1)))
    (if arg2
	(progn
	  (if (atom arg2)
	      (setf a2 (gethash arg2 *bindings*))
	      (setf a2 (match arg2)))))
    (funcall fn a1 a2)))
  
;;;; Main functions
;;;;

;;; main shell REPL function
(defun s-shell ()
  (loop while (null *quit*) do
     (format t "S-SHELL> ")
       (format t "~a~%" (match (read))))
  (setf *quit* nil))

;;; match function
;;; This function is at the heart of the expert shell.  It
;;; determines the type of expr looking at the first element,
;;; and either calls a function or recurses from there.
;;;
;;; Matching algorithm
;;;
;;; If first element is a (1) mapped function, Then
;;;     Call function with rest of expression
;;; Else If first element is a (2) bound variable, Then
;;;     If single element only, Then
;;;         Create a new bound variable using the first element
;;;         as a name.
;;;     Else // Assume a pair
;;;         Assign the second element value to the first element
;;;         variable.
(defun match (expr)
  (let* ((op (gethash (first expr) *functions*))
	 (key (first expr))
	 (value (gethash (first expr) *bindings*))
	 (re (cdr expr)))
;    (format t "op= ~a,key= ~a, value= ~a, re= ~a~%" op key value re)
    (cond (op
	   (if re
	       (funcall op re)
	       (funcall op)))
	  (value
	   (if (second expr)
	       (setf (gethash key *bindings*) (second expr))
	       value))
	  ((listp expr)
	   (progn
	     (if (first expr) (match (first expr)))
	     (if (cdr expr) (match (cdr expr))))))))

;;;; Main entry point
;(match '(assert west west))
;(match '(assert east east))
;(match '(assert farmer east))
;(match '(assert goat east))
;(match '(assert wolf east))
;(match '(assert cabbage east))

;;; Farmer-wolf-goat-cabbage production rules

;; move-farmer rule
;(match '(defrule move-farmer (?and (?~ (?= goat cabbage)) (?~ (?= goat wolf))) (assert (?if (?= farmer east) (assert farmer west) (assert farmer east)))))

;; move-farmer-goat rule
;(match '(defrule move-farmer-goat (?= farmer goat) (assert (?if (?= farmer east) ((assert farmer west) (assert goat west)) ((assert farmer east) (assert goat east))))))

;;; move-farmer-cabbage rule
;(match '(defrule move-farmer-cabbage (?and (?= farmer cabbage) (?~ (?= wolf goat))) (assert (?if (?= farmer east) ((assert farmer west) (assert cabbage west)) ((assert farmer east) (assert cabbage east))))))

;; move-farmer-wolf rule
;(match '(defrule move-farmer-wolf (?and (?= farmer wolf) (?~ (?= goat cabbage))) (assert (?if (?= farmer east) ((assert farmer west) (assert wolf west)) ((assert farmer east) (assert wolf east))))))

;; found-goal rule
;(match '(defrule found-goal (?and (?= farmer west) (?and (?= goat west) (?and (?= wolf west) (?= cabbage west)))) (show-rules)))

;(s-shell)
