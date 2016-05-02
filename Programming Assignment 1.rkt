; Timothy Kuo - tyk3 - Programming Excercise 1

;inorder? takes a list of numbers and returns #t if the numbers are in non-decreasing order 
(define inorder?
  (lambda (l)
    (cond
      ((null? l) #t)
      ((and (pair? (cdr l)) (> (car l) (car (cdr l)))) #f)
      (else (inorder? (cdr l))))))

;better version: you can include the (pair? (cdr l)) to be (or (null? (l)) (null? (cdr l))) and then compare in the second line

; dotproduct takes two lists of numbers and computes the dot product of the vectors. Ignores extra numbers of longer list
(define dotproduct
  (lambda (l1 l2)
    (cond
      ((or (null? l2) (null? l1)) 0)
      (else (+ (* (car l1) (car l2)) (dotproduct (cdr l1) (cdr l2)))))))

; helper method for squareroot that returns the next best guess in newton's method
(define newtons
  (lambda (o v)
    (- o (/ (- (* o o) v) (* 2 o)))))

; squareroot takes two numbers, a value and an iteration. Iteration >= 0.  
(define squareroot
  (lambda (v i)
    (cond
      ((zero? i) v)
      (else (newtons (squareroot v (- i 1)) v)))))

; removesubsequence takes two lists of atoms. The first list is a subsequence of the first list.  The method
; should return the second list with the first occurence of each atom in the subsequence removed. 
(define removesubsequence
  (lambda (l1 l2)
    (cond
      ((null? l1) l2)
      ((null? l2) '())
      ((eq? (car l1) (car l2)) (removesubsequence (cdr l1) (cdr l2)))
      (else (cons (car l2) (removesubsequence l1 (cdr l2)))))))

;helper method for reverse*. myappend appends the first list with the second list 
(define myappend
  (lambda (k l)
    (cond
      ((null? k) l)
      ((null? l) k)
      (else (cons (car k) (myappend (cdr k) l))))))

; helper method, atom? returns true if x is not null and not a pair
(define (atom? x) (and (not (null? x)) (not (pair? x))))

;reverse* takes a nested list and reverses the content of the list and all nested lists 
(define reverse*
  (lambda (l)
    (cond
      ((null? l) '())
      ((atom? (car l)) (myappend (reverse* (cdr l)) (cons (car l) '())))
      (else (myappend (reverse* (cdr l)) (cons (reverse* (car l)) '()))))))

;reverse using an accumulator, makes it linear instead of n^2
(define reverse-acc
  (lambda (l acc)
    (cond
      ((null? l) acc)
      ((pair? (car l)) (reverse-acc (cdr l) (cons (reverse-acc (car l) '()) acc)))
      (else (reverse-acc (cdr l) (cons (car l) acc))))))
  
; first* takes a list of lists and returns the first atom that appears in the list, regardless of how nested it is
(define first*
  (lambda (l)
  (cond
    ((null? l) l)
    ((atom? (car l)) (car l))
    (else (first* (car l))))))

; last* takes a list of lists and returns the last atom that appears in the list, regardless of how nested it is 
(define last*
  (lambda (l)
    (cond
      ((null? l) l)
      ((pair? (cdr l)) (last* (cdr l)))
      ((atom? (car l)) (car l))
      (else (last* (car l))))))

;helper function for numorder*?. sums up all the numbers in a list of lists
(define sumnumbers*
  (lambda (l)
    (cond
      ((null? l) 0)
      ((number? (car l)) (+ (car l) (sumnumbers* (cdr l))))
      ((pair? (car l)) (+ (sumnumbers* (car l)) (sumnumbers* (cdr l))))
      (else (sumnumbers* (cdr l))))))

;numorder*? takes a possibly nested list of numbers. returns #t if the values of the entires in the list are in
;non-decreasing order.  The value of a number is a number, but the value of a list is the sum of the values in it 
(define numorder*?
  (lambda (l)
    (cond
      ((null? l) #t)
      ((and (list? (car l)) (not (numorder*? (car l)))) #f) 
      ((and (pair? (cdr l)) (and (and (list? (car l)) (number? (car (cdr l)))) (> (sumnumbers* (car l)) (car (cdr l))))) #f) ;list vs number
      ((and (pair? (cdr l)) (and (and (list? (car l)) (list? (car (cdr l)))) (> (sumnumbers* (car l)) (sumnumbers* (car (cdr l)))))) #f) ;list vs list
      ((and (pair? (cdr l)) (and (and (number? (car l)) (number? (car (cdr l)))) (> (car l) (car (cdr l))))) #f) ;number vs number
      ((and (pair? (cdr l)) (and (and (number? (car l)) (list? (car (cdr l)))) (> (car l) (sumnumbers* (car (cdr l)))))) #f) ;number vs list
      (else (numorder*? (cdr l))))))

;abstract the idea of the value of an element
(define valueof
  (lambda (e)
    (if (list? e)
        (sumnumbers* e)
        e)))

;better version of numorder*?
(define numorder*?
  (lambda (l)
    ((null? l) #t)
    ((and (list? (car l)) (null? (cdr l))) (numorder*? (car l)))
    ((null? (cdr l)) #t)
    ((> (valueof (car l)) (valueof (cadr l))) #f)
    ((list? (car l)) (and (numorder*? (car l)) (numorder*? (cdr l))))
    (else (numorder*? (cdr l)))))

;Helper method for vectormult. Removes the first column of the matrix
(define removeFirstCol
  (lambda (l)
    (cond
      ((null? l) `())
      (else (cons  (cdr (car l)) (removeFirstCol (cdr l)))))))

;Helper method for vectormult. Returns the first column of the matrix
(define getFirstCol
  (lambda (l)
    (cond
      ((null? l) '())
      (else (cons (first* l) (getFirstCol (cdr l)))))))

;vectormult takes a row vector and matrix and multiplies the vector times the matrix. Result: vector where the
;ith element of the result is the dotproduct of the input vector and the ith column of the matrix.
(define vectormult
  (lambda (v m)
    (cond
      ((null? (car m)) '())
      (else (cons (dotproduct v (getFirstCol m)) (vectormult v (removeFirstCol m)))))))

;matrixmultiply takes two matrices and multiplies them. Assume number of columns of the first matrix is
;equal to the number of rows of the second matrix.
(define matrixmultiply
  (lambda (m1 m2)
    (cond
      ((null? m1) '())
      (else (cons (vectormult (car m1) m2) (matrixmultiply (cdr m1) m2))))))
      