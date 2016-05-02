; Timothy Kuo - tyk3 - Programming Excercise 2

;1. dotproduct takes two vectors and computes the dot products of the vectors
(define dotproduct
  (lambda (l1 l2 return)
    (if (or (null? l1) (null? l2))
        (return 0)
        (dotproduct (cdr l1) (cdr l2) (lambda (v) (return (+ v (* (car l1) (car l2)))))))))

;2. removesubsequence removes the first occurence of the subsequence (l1) from l2
(define removesubsequence
  (lambda (l1 l2 return)
    (cond
      ((null? l1) (return l2))
      ((null? l2) (return '()))
      ((eq? (car l1) (car l2)) (removesubsequence (cdr l1) (cdr l2) return))
      (else (removesubsequence l1 (cdr l2) (lambda (v) (return (cons (car l2) v))))))))

;3. sqaurerroot takes a value and an iteration and computes the squareroot using Newton's method
(define squareroot
  (lambda (v i return)
    (if (zero? i)
        (return v)
        (squareroot v (- i 1) (lambda (o) (return (- o (/ (- (* o o) v) (* 2 o)))))))))

;4. replaceall* takes two atoms and a nested list and replaces all occurences of the 1st atom with the 2nd atom
(define replaceall*
  (lambda (a1 a2 l return)
    (cond
      ((null? l) (return '()))
      ((eq? a1 (car l)) (replaceall* a1 a2 (cdr l) (lambda (v) (return (cons a2 v)))))
      ((list? (car l)) (replaceall* a1 a2 (car l) (lambda (v1) (replaceall* a1 a2 (cdr l) (lambda (v2) (return (cons v1 v2)))))))
      (else (replaceall* a1 a2 (cdr l) (lambda (v) (return (cons (car l) v))))))))

;5a. helper method for reverse - appends two lists in cps style
(define my-append-cps
  (lambda (l1 l2 return)
    (if (null? l1)
        (return l2)
        (my-append-cps (cdr l1) l2 (lambda (v) (return (cons (car l1) v)))))))

;5. reverse* takes a nested list and reverses the contents of the list and all nested lists
(define reverse*
  (lambda (l return)
    (cond
      ((null? l) (return '()))
      ((list? (car l)) (reverse* (cdr l) (lambda (v1) (reverse* (car l) (lambda (v2) (my-append-cps v1 (cons v2 '()) return))))))
      (else (reverse* (cdr l) (lambda (v) (my-append-cps v (cons (car l) '()) return)))))))

;6a. Helper method for vectormult. Removes the first column of the matrix
(define removeFirstCol
  (lambda (m return)
    (cond
      ((null? m) (return `()))
      (else (removeFirstCol (cdr m) (lambda (v) (return (cons (cdr (car m)) v))))))))

;6b. Helper method for vectormult. Returns the first column of the matrix
(define getFirstCol
  (lambda (m return)
    (cond
      ((null? m) (return '()))
      (else (getFirstCol (cdr m) (lambda (v) (return (cons (car (car m)) v))))))))

;6. vectormult takes a row vector and matrix and multiplies the vector with the matrix
(define vectormult
  (lambda (v m return)
    (cond
      ((or (null? m) (null? (car m))) (return '()))
      (else (vectormult v (removeFirstCol m (lambda (v) v))
                        (lambda (v1) (return (cons (dotproduct v (getFirstCol m (lambda (v) v)) (lambda (v) v)) v1))))))))

;7. matrixmultiply takes two matrices and multiples them together
(define matrixmultiply
  (lambda (m1 m2 return)
    (cond
      ((null? m1) (return '()))
      (else (matrixmultiply (cdr m1) m2 (lambda (v) (return (cons (vectormult (car m1) m2 (lambda (v) v)) v))))))))

;8. removesubsequence* takes a list of atoms and a general list and returns the second list with the first occurene of the subsequence removed
(define removesubsequence*
  (lambda (l1 l2 return)
    (cond
      ((or (null? l2) (null? l1)) (return l1 l2))
      ((pair? (car l2)) (removesubsequence* l1 (car l2) (lambda (v1 v2)
                                                          (removesubsequence* v1 (cdr l2) (lambda (v3 v4) (return v3 (cons v2 v4)))))))
      ((eq? (car l1) (car l2)) (removesubsequence* (cdr l1) (cdr l2) return))
      (else (removesubsequence* l1 (cdr l2) (lambda (v1 v2) (return l1 (cons (car l2) v2))))))))

;9. suffix takes an atom and a list and returns a list containing all the elements after the last occurence of the atom
(define suffix
  (lambda (a l)
    (letrec ((suffix-cps (lambda (l return break)
                   (cond
                     ((null? l) (return '()))
                     (else (suffix-cps (cdr l) (lambda (v) (cond
                                                               ((eq? a (car l)) (break v))
                                                               (else (return (cons (car l) v))))) break))))))
      (suffix-cps l (lambda (v) v) (lambda (v) v)))))

;10. suffix2 takes and atom and a list and returns a list containing all the elements after the last occurence of the atom
(define suffix2
  (lambda (a l)
    (call/cc
     (lambda (break)
       (letrec ((suffix-callcc (lambda (l return)
                               (cond
                                 ((null? l) (return '()))
                                 ((eq? a (car l)) (suffix-callcc (cdr l) break))
                                 (else (suffix-callcc (cdr l) (lambda (v) (return (cons (car l) v)))))))))
         (suffix-callcc l (lambda (v) v)))))))