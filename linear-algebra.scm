(module linear-algebra *
(import chicken (except scheme magnitude) extras data-structures)
(use define-structure srfi-1 traversal AD files)

(define *linear-algebra:epsilon* 1e-6)

(define pi (acos -1.0))

(define half-pi (/ pi 2.0))

(define two-pi (* 2.0 pi))

(define minus-pi (- pi))

(define two-pi/360 (/ two-pi 360.0))

(define three-sixty/two-pi (/ 360.0 two-pi))

;;; Vectors

(define-structure line-segment p q)

(define (p l) (line-segment-p l))

(define (q l) (line-segment-q l))

(define (x v) (vector-ref v 0))

(define (y v) (vector-ref v 1))

(define (z v) (vector-ref v 2))

(define (dot u v) (qmap-reduce-vector +-two 0 *-two u v))

(define (cross-2d u v)			;return scalar z-component
 (- (* (x u) (y v)) (* (y u) (x v))))

(define (cross u v)
 (vector (- (* (y u) (z v)) (* (y v) (z u)))
	 (- (* (x v) (z u)) (* (x u) (z v)))
	 (- (* (x u) (y v)) (* (x v) (y u)))))

(define (v+ u v) (map-vector +-two u v))

(define (v- u v) (map-vector --two u v))

(define (k*v k u) (map-vector (lambda (x) (* k x)) u))

(define (v= u v) (every-vector =-two u v))

(define (rotate-90 u) (vector (- (y u)) (x u)))

(define (rotate-180 u) (vector (- (x u)) (- (y u))))

(define (rotate-270 u) (vector (y u) (- (x u))))

(define (perpendicular? u v) (zero? (dot u v)))

(define (parallel? u v) (perpendicular? (rotate-90 u) v))

(define (magnitude-squared v) (dot v v))

(define (magnitude v) 
 (if (number? v)
     (abs v)
     (sqrt (magnitude-squared v))))

(define (unit v) (k*v (/ (magnitude v)) v))

(define (distance-squared u v) (magnitude-squared (v- v u)))

(define (distance u v) (sqrt (distance-squared u v)))

(define (line-tangent l) (unit (v- (line-segment-q l) (line-segment-p l))))

(define (normal-2d l)
 (unit (vector (- (y (line-segment-p l)) (y (line-segment-q l)))
	       (- (x (line-segment-q l)) (x (line-segment-p l))))))

(define (line-segment-length l)
 (distance (line-segment-p l) (line-segment-q l)))

(define (collinear? l1 l2)
 (and (parallel? (v- (q l1) (p l1)) (v- (p l2) (p l1)))
      (parallel? (v- (q l1) (p l1)) (v- (q l2) (p l1)))
      (parallel? (v- (q l2) (p l2)) (v- (p l1) (p l2)))
      (parallel? (v- (q l2) (p l2)) (v- (q l1) (p l2)))))

(define (point-on-line-segment? r l)
 (and (parallel? (v- (q l) (p l)) (v- r (p l)))
      (<= (min (x (p l)) (x (q l))) (x r) (max (x (p l)) (x (q l))))
      (<= (min (y (p l)) (y (q l))) (y r) (max (y (p l)) (y (q l))))))

(define (intersection-point l1 l2)
 (let ((a (invert-matrix (vector (vector (- (y (p l1)) (y (q l1)))
					 (- (x (q l1)) (x (p l1))))
				 (vector (- (y (p l2)) (y (q l2)))
					 (- (x (q l2)) (x (p l2))))))))
  (and a (m*v a (vector (+ (* (- (y (p l1)) (y (q l1))) (x (p l1)))
			   (* (- (x (q l1)) (x (p l1))) (y (p l1))))
			(+ (* (- (y (p l2)) (y (q l2))) (x (p l2)))
			   (* (- (x (q l2)) (x (p l2))) (y (p l2)))))))))

(define (clockwise-angle? u v w)
 (if (negative? (x u))
     (if (negative? (y u))
	 ;; U is in third quadrant
	 (clockwise-angle? (rotate-180 u) (rotate-180 v) (rotate-180 w))
	 ;; U is in second quadrant
	 (clockwise-angle? (rotate-270 u) (rotate-270 v) (rotate-270 w)))
     (if (negative? (y u))
	 ;; U is in fourth quadrant
	 (clockwise-angle? (rotate-90 u) (rotate-90 v) (rotate-90 w))
	 ;; U is in first quadrant
	 (if (negative? (x v))
	     (if (negative? (y v))
		 ;; V is in third quadrant
		 (if (negative? (x w))
		     (if (negative? (y w))
			 ;; W is in third quadrant
			 (clockwise-angle? v w u)
			 ;; W is in second quadrant
			 #t)
		     (if (negative? (y w))
			 ;; W is in fourth quadrant
			 #f
			 ;; W is in first quadrant
			 (clockwise-angle? w u v)))
		 ;; V is in second quadrant
		 (if (negative? (y w))
		     ;; W is in third or fourth quadrant
		     #f
		     (if (negative? (x w))
			 ;; W is in second quadrant
			 (clockwise-angle? v w u)
			 ;; W is in first quadrant
			 (clockwise-angle? w u v))))
	     (if (negative? (y v))
		 ;; V is in fourth quadrant
		 (if (negative? (x w))
		     ;; W is in second or third quadrant
		     #t
		     (if (negative? (y w))
			 ;; W is in fourth quadrant
			 (clockwise-angle? v w u)
			 ;; W is in first quadrant
			 (clockwise-angle? w u v)))
		 ;; V is in first quadrant
		 (if (negative? (x w))
		     ;; W is in second or third quadrant
		     (> (* (x v) (y u)) (* (x u) (y v)))
		     (if (negative? (y w))
			 ;; W is in fourth quadrant
			 (> (* (x v) (y u)) (* (x u) (y v)))
			 ;; W is in first quadrant
			 (or (and (> (* (x v) (y u)) (* (x u) (y v)))
				  (> (* (x w) (y v)) (* (x v) (y w))))
			     (and (> (* (x w) (y v)) (* (x v) (y w)))
				  (> (* (x u) (y w)) (* (x w) (y u))))
			     (and (> (* (x u) (y w)) (* (x w) (y u)))
				  (> (* (x v) (y u)) (* (x u) (y v))))))))))))

(define (clockwise-or-same-angle? u v w)
 (if (negative? (x u))
     (if (negative? (y u))
	 ;; U is in third quadrant
	 (clockwise-or-same-angle?
	  (rotate-180 u) (rotate-180 v) (rotate-180 w))
	 ;; U is in second quadrant
	 (clockwise-or-same-angle?
	  (rotate-270 u) (rotate-270 v) (rotate-270 w)))
     (if (negative? (y u))
	 ;; U is in fourth quadrant
	 (clockwise-or-same-angle? (rotate-90 u) (rotate-90 v) (rotate-90 w))
	 ;; U is in first quadrant
	 (if (negative? (x v))
	     (if (negative? (y v))
		 ;; V is in third quadrant
		 (if (negative? (x w))
		     (if (negative? (y w))
			 ;; W is in third quadrant
			 (clockwise-or-same-angle? v w u)
			 ;; W is in second quadrant
			 #t)
		     (if (negative? (y w))
			 ;; W is in fourth quadrant
			 #f
			 ;; W is in first quadrant
			 (clockwise-or-same-angle? w u v)))
		 ;; V is in second quadrant
		 (if (negative? (y w))
		     ;; W is in third or fourth quadrant
		     #f
		     (if (negative? (x w))
			 ;; W is in second quadrant
			 (clockwise-or-same-angle? v w u)
			 ;; W is in first quadrant
			 (clockwise-or-same-angle? w u v))))
	     (if (negative? (y v))
		 ;; V is in fourth quadrant
		 (if (negative? (x w))
		     ;; W is in second or third quadrant
		     #t
		     (if (negative? (y w))
			 ;; W is in fourth quadrant
			 (clockwise-or-same-angle? v w u)
			 ;; W is in first quadrant
			 (clockwise-or-same-angle? w u v)))
		 ;; V is in first quadrant
		 (if (negative? (x w))
		     ;; W is in second or third quadrant
		     (>= (* (x v) (y u)) (* (x u) (y v)))
		     (if (negative? (y w))
			 ;; W is in fourth quadrant
			 (>= (* (x v) (y u)) (* (x u) (y v)))
			 ;; W is in first quadrant
			 (or (and (>= (* (x v) (y u)) (* (x u) (y v)))
				  (>= (* (x w) (y v)) (* (x v) (y w))))
			     (and (>= (* (x w) (y v)) (* (x v) (y w)))
				  (>= (* (x u) (y w)) (* (x w) (y u))))
			     (and (>= (* (x u) (y w)) (* (x w) (y u)))
				  (>= (* (x v) (y u)) (* (x u) (y v))))))))))))

(define (cross? l1 l2)
 (or (and (clockwise-angle?
	   (v- (p l2) (p l1)) (v- (q l1) (p l1)) (v- (q l2) (p l1)))
	  (clockwise-angle?
	   (v- (q l1) (p l2)) (v- (q l2) (p l2)) (v- (p l1) (p l2)))
	  (clockwise-angle?
	   (v- (q l2) (q l1)) (v- (p l1) (q l1)) (v- (p l2) (q l1)))
	  (clockwise-angle?
	   (v- (p l1) (q l2)) (v- (p l2) (q l2)) (v- (q l1) (q l2))))
     (and (clockwise-angle?
	   (v- (q l2) (p l1)) (v- (q l1) (p l1)) (v- (p l2) (p l1)))
	  (clockwise-angle?
	   (v- (p l1) (p l2)) (v- (q l2) (p l2)) (v- (q l1) (p l2)))
	  (clockwise-angle?
	   (v- (p l2) (q l1)) (v- (p l1) (q l1)) (v- (q l2) (q l1)))
	  (clockwise-angle?
	   (v- (q l1) (q l2)) (v- (p l2) (q l2)) (v- (p l1) (q l2))))))

(define (intersect? l1 l2)
 (or (point-on-line-segment? (p l1) l2)
     (point-on-line-segment? (q l1) l2)
     (cross? l1 l2)))

(define (read-line-segments-from-file pathname)
 (define (read-line-segments-from-file port)
  (let loop ((l '()))
   (let* ((x1 (read port))
	  (y1 (read port))
	  (x2 (read port))
	  (y2 (read port)))
    (if (eof-object? y2)
	(reverse l)
	(loop (cons (make-line-segment (vector x1 y1) (vector x2 y2)) l))))))
 (if (string=? pathname "-")
     (read-line-segments-from-file (current-input-port))
     (call-with-input-file (pathname-replace-extension pathname "lines")
      read-line-segments-from-file)))

(define (write-line-segments-to-file line-segments pathname)
 (define (write-line-segments-to-file port)
  (for-each (lambda (l)
	     (write (x (line-segment-p l)) port)
	     (write-char #\space port)
	     (write (y (line-segment-p l)) port)
	     (write-char #\space port)
	     (write (x (line-segment-q l)) port)
	     (write-char #\space port)
	     (write (y (line-segment-q l)) port)
	     (newline port))
	    line-segments))
 (if (string=? pathname "-")
     (write-line-segments-to-file (current-output-port))
     (call-with-output-file (pathname-replace-extension pathname "lines")
      write-line-segments-to-file)))

;;; Matrices

(define (make-matrix m n . &rest)
 (cond ((null? &rest) (map-n-vector (lambda (i) (make-vector n)) m))
       ((null? (rest &rest))
	(map-n-vector (lambda (i) (make-vector n (first &rest))) m))
       (else (error "Too many arguments to MAKE-MATRIX"))))

(define (make-3-by-3-matrix a11 a12 a13 a21 a22 a23 a31 a32 a33)
 (vector (vector a11 a12 a13)
	 (vector a21 a22 a23)
	 (vector a31 a32 a33)))

(define (matrix-copy m)
 (map-vector (lambda (row) (map-vector identity row)) m))

(define (matrix-rows a) (vector-length a))

(define (matrix-columns a) (vector-length (vector-ref a 0)))

(define (matrix-ref a i j) (vector-ref (vector-ref a i) j))

(define (matrix-set! a i j x) (vector-set! (vector-ref a i) j x))

(define (matrix-row-ref a i) (vector-ref a i))

(define (matrix-column-ref a j) (map-vector (lambda (v) (vector-ref v j)) a))

(define (matrix-row-set! a i v) (vector-set! a i v))

(define (vector->row-matrix v) (vector v))

(define (vector->column-matrix v) (map-vector vector v))

(define (m+ a b) (map-vector v+ a b))

(define (m- a b) (map-vector v- a b))

(define (m*v a v) (map-vector (lambda (u) (dot u v)) a))

(define (transpose a)
 (map-n-vector (lambda (j) (matrix-column-ref a j)) (matrix-columns a)))

(define (outer-product f u v)
 (map-vector (lambda (ui) (map-vector (lambda (vj) (f ui vj)) v)) u))

(define (self-outer-product f v) (outer-product f v v))

(define (m* a b) (outer-product dot a (transpose b)))

(define (v*m v a) (m* (vector->row-matrix v) a))

(define (k*m k m)
 (map-vector (lambda (row) (map-vector (lambda (e) (* k e)) row)) m))

(define (determinant a)
 ;; The constants are hardwired to be inexact for efficiency.
 (unless (= (matrix-rows a) (matrix-columns a))
  (error "Can only find determinant of a square matrix"))
 (call-with-current-continuation
  (lambda (return)
   (let* ((n (matrix-rows a))
	  (b (make-matrix n n))
	  (d 1.0))
    (for-each-n
     (lambda (i)
      (for-each-n (lambda (j) (matrix-set! b i j (matrix-ref a i j))) n))
     n)
    (for-each-n
     (lambda (i)
      ;; partial pivoting reduces rounding errors
      (let ((greatest (abs (matrix-ref b i i)))
	    (index i))
       (for-each-from-a-up-to-b
	(lambda (j)
	 (let ((x (abs (matrix-ref b j i))))
	  (when (> x greatest) (set! index j) (set! greatest x))))
	(+ i 1)
	n)
       (when (= greatest 0.0) (return 0.0))
       (unless (= index i)
	(let ((v (matrix-row-ref b i)))
	 (matrix-row-set! b i (matrix-row-ref b index))
	 (matrix-row-set! b index v)
	 (set! d (- d))))
       (let ((c (matrix-ref b i i)))
	(set! d (* d c))
	(for-each-from-a-up-to-b
	 (lambda (j) (matrix-set! b i j (/ (matrix-ref b i j) c)))
	 i
	 n)
	(for-each-from-a-up-to-b
	 (lambda (j)
	  (let ((e (matrix-ref b j i)))
	   (for-each-from-a-up-to-b
	    (lambda (k)
	     (matrix-set!
	      b j k (- (matrix-ref b j k) (* e (matrix-ref b i k)))))
	    (+ i 1)
	    n)))
	 (+ i 1)
	 n))))
     n)
    d))))

(define (invert-matrix a)
 ;; The constants are hardwired to be inexact for efficiency.
 (unless (= (matrix-rows a) (matrix-columns a))
  (error "Can only invert a square matrix"))
 (call-with-current-continuation
  (lambda (abort)
   (let* ((n (matrix-rows a))
	  (c (make-matrix n n))
	  (b (make-matrix n n 0.0)))
    (for-each-n
     (lambda (i)
      (for-each-n (lambda (j) (matrix-set! c i j (matrix-ref a i j))) n))
     n)
    (for-each-n (lambda (i) (matrix-set! b i i 1.0)) n)
    (for-each-n
     (lambda (i)
      (when (zero? (matrix-ref c i i))
       (call-with-current-continuation
	(lambda (return)
	 (for-each-n (lambda (j)
		      (when (and (> j i) (not (zero? (matrix-ref c j i))))
		       (let ((e (vector-ref c i)))
			(vector-set! c i (vector-ref c j))
			(vector-set! c j e))
		       (let ((e (vector-ref b i)))
			(vector-set! b i (vector-ref b j))
			(vector-set! b j e))
		       (return #f)))
		     n)
	 (abort #f))))
      (let ((d (/ (matrix-ref c i i))))
       (for-each-n (lambda (j)
		    (matrix-set! c i j (* d (matrix-ref c i j)))
		    (matrix-set! b i j (* d (matrix-ref b i j))))
		   n)
       (for-each-n
	(lambda (k)
	 (let ((d (- (matrix-ref c k i))))
	  (unless (= k i)
	   (for-each-n
	    (lambda (j)
	     (matrix-set!
	      c k j (+ (matrix-ref c k j) (* d (matrix-ref c i j))))
	     (matrix-set!
	      b k j (+ (matrix-ref b k j) (* d (matrix-ref b i j)))))
	    n))))
	n)))
     n)
    b))))

(define (simplex a m1 m2 m3)
 (unless (and (>= m1 0)
	      (>= m2 0)
	      (>= m3 0)
	      (= (matrix-rows a) (+ m1 m2 m3 2)))
  (error "fuck-up"))
 (let* ((m12 (+ m1 m2 1))
	(m (- (matrix-rows a) 2))
	(n (- (matrix-columns a) 1))
	(l1 (make-vector (+ n 1)))
	(l2 (make-vector m))
	(l3 (make-vector m2))
	(nl1 n)
	(iposv (make-vector m))
	(izrov (make-vector n))
	(ip 0)
	(kp #f)
	(bmax #f))
  (define (simp1 mm abs?)
   (set! kp (vector-ref l1 0))
   (set! bmax (matrix-ref a mm kp))
   (do ((k 1 (+ k 1))) ((>= k nl1))
    (when (positive?
	   (if abs?
	       (- (abs (matrix-ref a mm (vector-ref l1 k))) (abs bmax))
	       (- (matrix-ref a mm (vector-ref l1 k)) bmax)))
     (set! kp (vector-ref l1 k))
     (set! bmax (matrix-ref a mm (vector-ref l1 k))))))
  (define (simp2)
   (set! ip 0)
   (let ((q1 0.0)
	 (flag? #f))
    (for-each-n
     (lambda (i)
      (if flag?
	  (when (< (matrix-ref a (vector-ref l2 i) kp) (- *linear-algebra:epsilon*))
	   (let ((q (/ (- (matrix-ref a (vector-ref l2 i) 0))
		       (matrix-ref a (vector-ref l2 i) kp))))
	    (cond
	     ((< q q1) (set! ip (vector-ref l2 i)) (set! q1 q))
	     ((= q q1)
	      (let ((qp 0.0)
		    (q0 0.0))
	       (let loop ((k 1))
		(when (<= k n)
		 (set! qp (/ (- (matrix-ref a ip k)) (matrix-ref a ip kp)))
		 (set! q0 (/ (- (matrix-ref a (vector-ref l2 i) k))
			     (matrix-ref a (vector-ref l2 i) kp)))
		 (when (= q0 qp) (loop (+ k 1)))))
	       (when (< q0 qp) (set! ip (vector-ref l2 i))))))))
	  (when (< (matrix-ref a (vector-ref l2 i) kp) (- *linear-algebra:epsilon*))
	   (set! q1 (/ (- (matrix-ref a (vector-ref l2 i) 0))
		       (matrix-ref a (vector-ref l2 i) kp)))
	   (set! ip (vector-ref l2 i))
	   (set! flag? #t))))
     m)))
  (define (simp3 one?)
   (let ((piv (/ (matrix-ref a ip kp)))
	 (m (- (matrix-rows a) 2))
	 (n (- (matrix-columns a) 1)))
    (for-each-n
     (lambda (ii)
      (unless (= ii ip)
       (matrix-set! a ii kp (* piv (matrix-ref a ii kp)))
       (for-each-n
	(lambda (kk)
	 (unless (= kk kp)
	  (matrix-set! a ii kk (- (matrix-ref a ii kk)
				  (* (matrix-ref a ip kk)
				     (matrix-ref a ii kp))))))
	(+ n 1))))
     (+ m (if one? 2 1)))
    (for-each-n
     (lambda (kk)
      (unless (= kk kp)
       (matrix-set! a ip kk (* (- piv) (matrix-ref a ip kk)))))
     (+ n 1))
    (matrix-set! a ip kp piv)))
  (define (pass2)
   (simp1 0 #f)
   (cond ((positive? bmax)
	  (simp2)
	  (cond ((zero? ip) #t)
		(else (simp3 #f)
		      (let ((t (vector-ref izrov (- kp 1))))
		       (vector-set! izrov (- kp 1)
				    (vector-ref iposv (- ip 1)))
		       (vector-set! iposv (- ip 1) t))
		      (pass2))))
	 (else (list iposv izrov))))
  (for-each-n
   (lambda (k)
    (vector-set! l1 k (+ k 1))
    (vector-set! izrov k k))
   n)
  (for-each-n
   (lambda (i)
    (when (negative? (matrix-ref a (+ i 1) 0)) (error "fuck-up"))
    (vector-set! l2 i (+ i 1))
    (vector-set! iposv i (+ n i)))
   m)
  (for-each-n (lambda (i) (vector-set! l3 i #t)) m2)
  (cond
   ((positive? (+ m2 m3))
    (for-each-n
     (lambda (k)
      (do ((i (+ m1 1) (+ i 1)) (sum 0.0 (+ sum (matrix-ref a i k))))
	((> i m) (matrix-set! a (+ m 1) k (- sum)))))
     (+ n 1))
    (let loop ()
     (define (one)
      (simp3 #t)
      (cond
       ((>= (vector-ref iposv (- ip 1)) (+ n m12 -1))
	(let loop ((k 0))
	 (cond
	  ((and (< k nl1) (not (= kp (vector-ref l1 k)))) (loop (+ k 1)))
	  (else (set! nl1 (- nl1 1))
		(do ((is k (+ is 1))) ((>= is nl1))
		 (vector-set! l1 is (vector-ref l1 (+ is 1))))
		(matrix-set! a (+ m 1) kp (+ (matrix-ref a (+ m 1) kp) 1))
		(for-each-n
		 (lambda (i) (matrix-set! a i kp (- (matrix-ref a i kp))))
		 (+ m 2))))))
       ((and (>= (vector-ref iposv (- ip 1)) (+ n m1))
	     (vector-ref l3 (- (vector-ref iposv (- ip 1)) m1 n)))
	(vector-set! l3 (- (vector-ref iposv (- ip 1)) m1 n) #f)
	(matrix-set! a (+ m 1) kp (+ (matrix-ref a (+ m 1) kp) 1))
	(for-each-n (lambda (i) (matrix-set! a i kp (- (matrix-ref a i kp))))
		    (+ m 2))))
      (let ((t (vector-ref izrov (- kp 1))))
       (vector-set! izrov (- kp 1) (vector-ref iposv (- ip 1)))
       (vector-set! iposv (- ip 1) t))
      (loop))
     (simp1 (+ m 1) #f)
     (cond
      ((<= bmax *linear-algebra:epsilon*)
       (cond ((< (matrix-ref a (+ m 1) 0) (- *linear-algebra:epsilon*)) #f)
	     ((<= (matrix-ref a (+ m 1) 0) *linear-algebra:epsilon*)
	      (let loop ((ip1 m12))
	       (cond
		((<= ip1 m)
		 (cond ((= (vector-ref iposv (- ip1 1)) (+ ip n -1))
			(simp1 ip1 #t)
			(cond ((positive? bmax) (set! ip ip1) (one))
			      (else (loop (+ ip1 1)))))
		       (else (loop (+ ip1 1)))))
		(else
		 (do ((i (+ m1 1) (+ i 1))) ((>= i m12))
		  (when (vector-ref l3 (- i m1 1))
		   (for-each-n
		    (lambda (k) (matrix-set! a i k (- (matrix-ref a i k))))
		    (+ n 1))))
		 (pass2)))))
	     (else (simp2) (if (zero? ip) #f (one)))))
      (else (simp2) (if (zero? ip) #f (one))))))
   (else (pass2)))))

;;; The constants in the following are hardwired to be inexact for efficiency.

(define (quadratic1 a b c)
 (let ((d (- (* b b) (* 4.0 a c))))
  (when (and (negative? d) (< (- d) *linear-algebra:epsilon*)) (set! d 0.0))
  (/ (+ (- b) (sqrt d)) (* 2.0 a))))

(define (quadratic2 a b c)
 (let ((d (- (* b b) (* 4.0 a c))))
  (when (and (negative? d) (< (- d) *linear-algebra:epsilon*)) (set! d 0.0))
  (/ (- (- b) (sqrt d)) (* 2.0 a))))

(define (jacobi a)
 (unless (and (= (matrix-rows a) (matrix-columns a))
	      (every-n (lambda (i)
			(every-n (lambda (j)
				  (= (matrix-ref a i j) (matrix-ref a j i)))
				 (matrix-rows a)))
		       (matrix-rows a)))
  (error "Can only compute eigenvalues/eigenvectors of a symmetric matrix"))
 (let* ((a (map-vector (lambda (row) (map-vector identity row)) a))
	(n (matrix-rows a))
	(d (make-vector n))
	(v (make-matrix n n 0.0))
	(b (make-vector n))
	(z (make-vector n 0.0)))
  (for-each-n (lambda (ip)
	       (matrix-set! v ip ip 1.0)
	       (vector-set! b ip (matrix-ref a ip ip))
	       (vector-set! d ip (matrix-ref a ip ip)))
	      n)
  (let loop ((i 0))
   ;; This was changed from 50 to 500 for center-surround.
   (when (> i 500) (error "Too many iterations in JACOBI"))
   (let ((sm (sum (lambda (ip)
		   (sum (lambda (ir)
			 (let ((iq (+ ip ir 1)))
			  (abs (matrix-ref a ip iq))))
			(- n ip 1)))
		  (- n 1))))
    (unless (zero? sm)
     (let ((tresh (if (< i 3) (/ (* 0.2 sm) (* n n)) 0.0)))
      (for-each-n
       (lambda (ip)
	(for-each-n
	 (lambda (ir)
	  (let* ((iq (+ ip ir 1))
		 (g (* 100.0 (abs (matrix-ref a ip iq)))))
	   (cond
	    ((and (> i 3)
		  (= (+ (abs (vector-ref d ip)) g) (abs (vector-ref d ip)))
		  (= (+ (abs (vector-ref d iq)) g) (abs (vector-ref d iq))))
	     (matrix-set! a ip iq 0.0))
	    ((> (abs (matrix-ref a ip iq)) tresh)
	     (let* ((h (- (vector-ref d iq) (vector-ref d ip)))
		    (t (if (= (+ (abs h) g) (abs h))
			   (/ (matrix-ref a ip iq) h)
			   (let ((theta (/ (* 0.5 h) (matrix-ref a ip iq))))
			    (if (negative? theta)
				(- (/ (+ (abs theta)
					 (sqrt (+ (* theta theta) 1.0)))))
				(/ (+ (abs theta)
				      (sqrt (+ (* theta theta) 1.0))))))))
		    (c (/ (sqrt (+ (* t t) 1.0))))
		    (s (* t c))
		    (tau (/ s (+ c 1.0)))
		    (h (* t (matrix-ref a ip iq))))
	      (define (rotate a i j k l)
	       (let ((g (matrix-ref a i j))
		     (h (matrix-ref a k l)))
		(matrix-set! a i j (- g (* s (+ h (* g tau)))))
		(matrix-set! a k l (+ h (* s (- g (* h tau)))))))
	      (vector-set! z ip (- (vector-ref z ip) h))
	      (vector-set! z iq (+ (vector-ref z iq) h))
	      (vector-set! d ip (- (vector-ref d ip) h))
	      (vector-set! d iq (+ (vector-ref d iq) h))
	      (matrix-set! a ip iq 0.0)
	      (for-each-n (lambda (j)
			   (cond ((< j ip) (rotate a j ip j iq))
				 ((< ip j iq) (rotate a ip j j iq))
				 ((< iq j) (rotate a ip j iq j)))
			   (rotate v j ip j iq))
			  n))))))
	 (- n ip 1)))
       (- n 1)))
     (for-each-n (lambda (ip)
		  (vector-set! b ip (+ (vector-ref b ip) (vector-ref z ip)))
		  (vector-set! d ip (vector-ref b ip))
		  (vector-set! z ip 0.0))
		 n)
     (loop (+ i 1)))))
  (for-each-n
   (lambda (i)
    (let ((k i)
	  (p (vector-ref d i)))
     (for-each-n
      (lambda (l)
       (let* ((j (+ i l 1)))
	(when (>= (vector-ref d j) p) (set! k j) (set! p (vector-ref d j)))))
      (- n i 1))
     (unless (= k i)
      (vector-set! d k (vector-ref d i))
      (vector-set! d i p)
      (for-each-n (lambda (j)
		   (let ((p (matrix-ref v j i)))
		    (matrix-set! v j i (matrix-ref v j k))
		    (matrix-set! v j k p)))
		  n))))
   (- n 1))
  (list d (transpose v))))

(define (eigenvalues a) (first (jacobi a)))

(define (eigenvectors a) (second (jacobi a)))

(define (vector->diagonal-matrix v)
 (let ((m (make-matrix (vector-length v) (vector-length v) 0.0)))
  (for-each-n (lambda (i) (matrix-set! m i i (vector-ref v i)))
	      (vector-length v))
  m))

(define (identity-matrix n) (vector->diagonal-matrix (make-vector n 1.0)))

(define (clip-eigenvalues a v)
 (let* ((j (jacobi a))
	(e (second j)))
  (m* (transpose e)
      (m* (vector->diagonal-matrix (map-vector max v (first j))) e))))

;;; The following two routines are limited to 2-by-2 matricies.

(define (eigenvector-angle1 m)
 (if (and (< (abs (matrix-ref m 1 0)) *linear-algebra:epsilon*)
	  (< (abs (matrix-ref m 0 1)) *linear-algebra:epsilon*))
     (if (> (matrix-ref m 1 1) (matrix-ref m 0 0)) half-pi 0.0)
     (atan (matrix-ref m 1 0)
	   (- (vector-ref (eigenvalues m) 0) (matrix-ref m 1 1)))))

(define (eigenvector-angle2 m)
 (if (and (< (abs (matrix-ref m 1 0)) *linear-algebra:epsilon*)
	  (< (abs (matrix-ref m 0 1)) *linear-algebra:epsilon*))
     (if (<= (matrix-ref m 1 1) (matrix-ref m 0 0)) half-pi 0.0)
     (atan (matrix-ref m 1 0)
	   (- (vector-ref (eigenvalues m) 1) (matrix-ref m 1 1)))))

;;; Sparse Matrices

(define-structure sparse-matrix row column blank)

(define-structure sparse-matrix-row element i up down)

(define-structure sparse-matrix-column element j left right)

(define-structure sparse-matrix-element value i up down j left right)

(define (create-sparse-matrix blank)
 (make-sparse-matrix #f #f blank))

(define (sparse-matrix-ref sparse-matrix i j)
 ;; note: Could do different traversals.
 ;; note: Could terminate sooner relying upon ordering.
 ;; note: Could make equality predicate a parameter and have different values
 ;;       for rows and columns.
 (let loop ((sparse-matrix-row (sparse-matrix-row sparse-matrix)))
  (if sparse-matrix-row
      (if (= (sparse-matrix-row-i sparse-matrix-row) i)
	  (let loop ((sparse-matrix-element
		      (sparse-matrix-row-element sparse-matrix-row)))
	   (if sparse-matrix-element
	       (if (= (sparse-matrix-element-j sparse-matrix-element) j)
		   (sparse-matrix-element-value sparse-matrix-element)
		   (loop (sparse-matrix-element-right sparse-matrix-element)))
	       (sparse-matrix-blank sparse-matrix)))
	  (loop (sparse-matrix-row-down sparse-matrix-row)))
      (sparse-matrix-blank sparse-matrix))))
)
