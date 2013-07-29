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

(define (sqr x) (* x x))

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

(define (k*v k v) (map-vector (lambda (x) (* k x)) v))
(define (v*k v k) (k*v k v))

(define (v/k v k) (k*v (/ 1 k) v))

(define (v* v u) (map-vector *-two v u))
(define (v/ v u) (map-vector /-two v u))

(define (k+v k v) (map-vector (lambda (x) (+ k x)) v))
(define (v+k v k) (k+v k v))

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

(define (matrix? v)
 (and (vector? v) (or (= (vector-length v) 0) (vector? (vector-ref v 0)))))

(define (list->matrix l) (list->vector (map list->vector l)))

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

(define (m+k m k) (map-matrix (lambda (e) (+ e k)) m))
(define (k+m k m) (m+k m k))

(define (m+k-diagonal m k)
 (map-vector (lambda (x i) (map-vector (lambda (e j) (if (= i j) (+ e k) e)) x)) m))

(define (m*v a v) (map-vector (lambda (u) (dot u v)) a))

(define (matrix-transpose a)
 (map-n-vector (lambda (j) (matrix-column-ref a j)) (matrix-columns a)))

(define (outer-product f u v)
 (map-vector (lambda (ui) (map-vector (lambda (vj) (f ui vj)) v)) u))

(define (self-outer-product f v) (outer-product f v v))

(define (m* a b) (outer-product dot a (matrix-transpose b)))

(define (v*m v a) (m* (vector->row-matrix v) a))

(define (k*m k m) (map-vector (lambda (row) (map-vector (lambda (e) (* k e)) row)) m))
(define (m*k m k) (k*m k m))
(define (m/k m k) (k*m (/ 1 k) m))

(define (m*. m1 m2) (map-indexed-matrix (lambda (e1 i j) (* e1 (matrix-ref m2 i j))) m1))
(define (m/. m1 m2) (map-indexed-matrix (lambda (e1 i j) (/ e1 (matrix-ref m2 i j))) m1))

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
  (list d (matrix-transpose v))))

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
  (m* (matrix-transpose e)
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

(define (left-pseudo-inverse m)
 (let ((inverse (invert-matrix (m* (matrix-transpose m) m))))
  (if inverse (m* inverse (matrix-transpose m)) #f)))

(define (right-pseudo-inverse m)
 (let ((inverse (invert-matrix (m* m (matrix-transpose m)))))
  (if inverse (m* (matrix-transpose m) inverse) #f)))

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

;;; Misc

(define (every-n-2d p v w)
 (every-n (lambda (a) (every-n (lambda (b) (p a b)) w)) v))
(define (every-n-3d p v w x)
 (every-n (lambda (a) (every-n-2d (lambda (b c) (p a b c)) w x)) v))
(define (every-n-4d p v w x y)
 (every-n-2d (lambda (a b) (every-n-2d (lambda (c d) (p a b c d)) x y)) v w))
(define (every-n-5d p v w x y z)
 (every-n (lambda (a) (every-n-4d (lambda (b c d e) (p a b c d e)) w x y z)) v))
(define (map-n-vector-2d f m n)
 (map-n-vector (lambda (a) (map-n-vector (lambda (b) (f a b)) n)) m))
(define (map-n-vector-3d f m n p)
 (map-n-vector (lambda (a) (map-n-vector-2d (lambda (b c) (f a b c)) n p)) m))
(define (map-n-vector-4d f m n p q)
 (map-n-vector-2d (lambda (a b) (map-n-vector-2d (lambda (c d) (f a b c d)) p q)) m n))
(define (map-n-vector-5d f m n p q r)
 (map-n-vector-3d (lambda (a b c) (map-n-vector-2d (lambda (d e) (f a b c d e)) q r)) m n p))
(define (product-2d f m n) (product (lambda (a) (product (lambda (b) (f a b)) n)) m))
(define (ref-1d m a) (vector-ref m a))
(define (ref-2d m a b) (matrix-ref m a b))
(define (ref-3d m a b c) (matrix-ref (vector-ref m a) b c))
(define (ref-4d m a b c d) (matrix-ref (matrix-ref m a b) c d))
(define (ref-5d m a b c d e) (matrix-ref (ref-3d m a b c) d e))
(define (sum-2d f m n) (sum (lambda (a) (sum (lambda (b) (f a b)) n)) m))
(define (sum-3d f m n p) (sum-2d (lambda (a b) (sum (lambda (c) (f a b c)) p)) m n))
(define (sum-4d f m n p q) (sum-2d (lambda (a b) (sum-2d (lambda (c d) (f a b c d)) p q)) m n))
(define (sum-pairs f m) (sum (lambda (a) (sum (lambda (b) (f a b)) a)) m))
(define (vector-sum f n i)
 (let loop ((n (- n 1)) (c i))
  (if (negative? n) c (loop (- n 1) (v+ c (f n))))))
(define (vector-sum-2d f m n i)
 (vector-sum (lambda (a) (vector-sum (lambda (b) (f a b)) n i)) m i))
(define (matrix-sum f n i)
 (let loop ((n (- n 1)) (c i))
  (if (negative? n) c (loop (- n 1) (m+ c (f n))))))
(define (matrix-sum-2d f m n i)
 (matrix-sum (lambda (a) (matrix-sum (lambda (b) (f a b)) n i)) m i))
(define (v*m*v v m) (dot v (m*v m v)))
(define (sum-f f l) (qmap-reduce + 0 f l))
(define (sum-vector v) (qreduce-vector + v 0))
(define (sum-vector-f f v) (qmap-reduce-vector + 0 f v))

(define (append-vector vec1 vec2)
 (let ((l1 (vector-length vec1))
       (l2 (vector-length vec2)))
  (map-n-vector
   (lambda (i)
    (if (< i l1) (vector-ref vec1 i) (vector-ref vec2 (- i l1))))
   (+ l1 l2))))

(define (shape-matrix v c)
 (let* ((r (/ (vector-length v) c))
	(m (make-vector r)))
  (for-each-n
   (lambda (i) (vector-set! m i (subvector v (* i c) (* (+ i 1) c))))
   r)
  m))

(define (unshape-matrix m)
 (if (and (not (equal? m '#())) (matrix? m))
     (unshape-matrix (qreduce-vector append-vector m '#()))
     m))

(define (crop m x y w h)
 (map-vector
  (lambda (row)
   (subvector row x (+ x w)))
  (subvector m y (+ y h))))

(define (submatrix m x-offset y-offset x-size y-size)
 (define (safe-matrix-ref m r c)
  (if (and (< r (matrix-rows m)) (< c (matrix-columns m)))
      (matrix-ref m r c)
      #f))
 (map-n-vector
  (lambda (x)
   (map-n-vector
    (lambda (y) (safe-matrix-ref m (+ x x-offset) (+ y y-offset)))
    y-size))
  x-size))

(define (matrix-ref-nd m . is)
 (if (= (length is) 1)
     (vector-ref m (first is))
     (apply matrix-ref-nd `(,(vector-ref m (first is)) ,@(rest is)))))
(define (matrix-3d-ref a s i j) (matrix-ref-nd a s i j))

(define (matrix-set-nd! m v . is)
 (if (= (length is) 1)
     (begin (write m) (newline) (vector-set! m (first is) v))
     (apply matrix-set-nd! `(,(vector-ref m (first is)) ,v ,@(rest is)))))
(define (matrix-3d-set! a v s i j) (matrix-set-nd! a v s i j))

(define (map-matrix-nd f m n)
 (if (= n 1)
     (map-vector f m)
     (map-vector (lambda (m) (map-matrix-nd f m (- n 1))) m)))
(define (for-each-matrix-nd f m n)
 (if (= n 1)
     (for-each-vector f m)
     (for-each-vector (lambda (m) (for-each-matrix-nd f m (- n 1))) m)))
(define (map-matrix f m) (map-matrix-nd f m 2))
(define (for-each-matrix f m) (for-each-matrix-nd f m 2))
(define (map-matrix-3d f m) (map-matrix-nd f m 3))
(define (for-each-matrix-3d f m) (for-each-matrix-nd f m 3))

(define (map-n-matrix f i j)
 (map-n-vector (lambda (i) (map-n-vector (lambda (j) (f i j)) j)) i))
(define (for-each-n-matrix f i j)
 (for-each-n (lambda (i) (for-each-n (lambda (j) (f i j)) j)) i))

(define (map-indexed-matrix f m)
 (map-indexed-vector (lambda (r i) (map-indexed-vector (lambda (c j) (f c i j)) r)) m))
(define (for-each-indexed-matrix f m)
 (for-each-indexed-vector
  (lambda (r i) (for-each-indexed-vector (lambda (c j) (f c i j)) r))
  m))
(define (map-indexed-matrix-3d f p)
 (map-indexed-vector
  (lambda (s l) (map-indexed-matrix (lambda (c i j) (f c l i j)) s))
  p))
(define (for-each-indexed-matrix-3d f p)
 (for-each-indexed-vector
  (lambda (s l) (for-each-indexed-matrix (lambda (c i j) (f c l i j)) s))
  p))

;;; Statistics, this probably doesn't belong here

(define (list-mean p)
 (if (vector? (car p))
     (k*v  (/ 1 (length p)) (qreduce v+ p 0))
     (/ (qreduce + p 0) (length p))))

(define (list-covariance l)
 (let ((mu (list-mean l)))
  (k*m (/ (length l))
       (qreduce m+ (map (lambda (e) (self-outer-product * (v- e mu))) l) #f))))

(define (list-variance s)
 (let ((mu (list-mean s)))
  (/ (qreduce + (map (lambda (s) (sqr (- s mu))) s) 0) (length s))))

(define (list-skewness l)
 (let ((mu (list-mean l))
       (sigma (list-variance l)))
  (/ (* (/ (length l)) (qreduce + (map (lambda (e) (expt (-  e mu) 3)) l) 0))
     (expt sigma (/ 3 2)))))

(define (list-kurtosis l)
 (let ((mu (list-mean l))
       (sigma (list-variance l)))
  (- (/ (* (/ (length l)) (qreduce + (map (lambda (e) (expt (-  e mu) 4)) l) 0))
	(sqr sigma))
     3)))

(define (list-correlation l1 l2)
 (let ((mu1 (list-mean l1)) (mu2 (list-mean l2))
       (s1 (sqrt (list-variance l1))) (s2 (sqrt (list-variance l2))))
  (/
   (qreduce + (map (lambda (v1 v2) (* (- v1 mu1) (- v2 mu2))) l1 l2) 0)
   (* (- (length l1) 1) s1 s2))))

(define (vector-mean v)
 (/ (qreduce-vector + v 0) (vector-length v)))

(define (vector-variance v)
 (let ((mu (vector-mean v)))
  (/ (qmap-reduce-vector + 0 (lambda (s) (sqr (- s mu))) v) (vector-length v))))

(define (vector-skewness v)
 (let ((mu (vector-mean v))
       (sigma (vector-variance v)))
  (/ (* (/ (vector-length v)) (qmap-reduce-vector + 0 (lambda (e) (expt (- e mu) 3)) v))
     (expt sigma (/ 3 2)))))

(define (vector-kurtosis v)
 (let ((mu (vector-mean v))
       (sigma (vector-variance v)))
  (- (/ (* (/ (vector-length v)) (qmap-reduce-vector + 0 (lambda (e) (expt (- e mu) 4)) v))
	(sqr sigma))
     3)))

(define (vector-correlation v1 v2)
 (let ((mu1 (vector-mean v1)) (mu2 (vector-mean v2))
       (s1 (sqrt (vector-variance v1))) (s2 (sqrt (vector-variance v2))))
  (/
   (qmap-reduce-vector + 0 (lambda (v1 v2) (* (- v1 mu1) (- v2 mu2))) v1 v2)
   (* (- (length v1) 1) s1 s2))))

(define (coefficient-of-bimodality v)
 (cond ((list? v)
	(/ (+ 1 (sqr (list-skewness v))) (+ (list-kurtosis v) 3)))
       ((vector? v)
	(/ (+ 1 (sqr (vector-skewness v))) (+ (vector-kurtosis v) 3)))
       (else (error "coefficient-of-bimodality"))))

(define (vectors-mean values)
 (k*v (/ 1 (vector-length values)) (qreduce-vector v+ values #f)))

(define (vectors-variance mu values)
 (k*m (/ 1 (vector-length values))
      (qreduce-vector m+
		     (map-vector
		      (lambda (value)
		       (self-outer-product * (v- value mu)))
		      values)
		     #f)))

(define (mahalanobis-distance val mu isigma)
 (let ((dev (v- val mu)))
  (sqrt (abs (dot dev (m*v isigma dev))))))

(define (frequencies l)
 (let loop ((f '()) (l l))
  (if (null? l)
      f
      (loop (cons `(,(car l) ,(count (car l) l)) f)
	    (remove (car l) l)))))

)
