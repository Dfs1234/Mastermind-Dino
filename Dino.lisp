;;; Dino.lisp
;;; Mastermind solver for CSCI 350
;;; Truly Johnson, Andy Ko, Daven Liu, Xiaoning Wang

;;; *****************************
;;; VARIABLES
;;; *****************************
;; for main function:
(defvar *selected-function*) ;stores the function to use for the current tournament

;; repeatedly used variables:
(defvar *bulls* 0) 
(defvar *cows* 0)
(defvar *numOfGuesses* nil)
(defvar *guess* nil) ;stores guess
(defvar *numOfPos* nil)
(defvar *colors* nil)
(defvar *curColorPos* nil)
(defvar *correctColorPos* nil)

;; for baseline 1:
(defvar *combinations* nil);Holds a list of all combinations from colors of size 'board'.

;; for baseline 2:
(defvar *avoid-colors* nil) ;Stores list of colors which should be avoided. 
(defvar *permutations* nil) ;Holds list of all possible permutations generated from colors of size board.
(defvar *position* 1) ;Position while we are parsing through permutations

;; for baseline 3:
(defvar *quantities* NIL) ;stores quantities of each color

;; for baseline 4:
(defvar *inferences* NIL)
(defvar *gameover* NIL)
(defvar *N* 0)
(defvar *G* NIL)
(defvar *beingfixed* NIL)
(defvar *beingconsidered* NIL)
(defvar *gain* NIL)
(defvar totalnum nil)
(defvar tempnum nil)

;;for two-color alternating
(defvar *last-guess* NIL)
(defvar *two-colors* NIL)

;;for ab-color
(defvar *abcolors* '(A B))

;;for Only-once
(defvar *correctColors* nil)
(defvar *correctColorsWithPosition* nil)

;;for Mystery-2
(defvar *first_color* nil)
(defvar *second_color* nil)
(defvar *third_color* nil)
(defvar *color_list* nil)
(defvar *correct_first_color* nil)
(defvar *correct_second_color* nil)
(defvar *correct_third_color* nil)
(defvar *testIfCorrectAlgorithm* nil)
(defvar *correctAlgorithm* nil)
(defvar *nonColor* nil)
(defvar Color2 nil)
(defvar Color3 nil)
(defvar firstColor nil)
(defvar secondColor nil)
(defvar thirdColor nil)
(defvar *needpermutation* nil)
(defvar *permutationPos* nil)
(defvar *permutationList* nil)

;; for local search
(defvar *found-colors* NIL) ;set to true once distribution of colors is found
(defvar *prepared* NIL) ; set to true once preparations are over (once *candidates* reaches *beam-width* for the first time)
(defvar *guess-index* 0) ;index of the last memeber of candidates a successor was generated from
(defvar *candidates* NIL) ;stores list of lists each containing a guess and the number of correct position of pins in that guess. form: ((guess-1 correctpins-1) ... (guess-n correctpins-n)
(defvar *already-guessed* NIL) ;stores list of previous guesses. form (guess-1 guess-2 ... guess-n)
(defvar *known-pegs* NIL) ;stores one correct peg in each position or NIL if correct peg for that position is unknown.
(defvar *wrong-pegs* NIL) ;stores a list of wrong pegs in each position or NIL
(defvar *last-i* NIL) ;stores one of the two indices (i) modified last time a successor was generated
(defvar *last-j* NIL) ;stores one of the two indices (j) modified last time a successor was generated

;;; **************************************
;;; MAIN FUNCTION - reroutes to another function depending on SCSA
;;; **************************************

(defun Dino (board colors SCSA last-response)
  (cond ((equal last-response nil) ;no guesses have been made yet - select a function based on SCSA being used
	 
	 (cond ((equal SCSA 'two-color-alternating)
		(setf *selected-function* 'dino-two-color-alternating))
	       ((equal SCSA 'first-and-last)
		(setf *selected-function* 'dino-first-and-last))
	       ((equal SCSA 'mystery-5)
		(setf *selected-function* 'dino-two-color-alternating))
	       (T
		(setf *selected-function* 'baseline-4-Dino)))))
  (cond ((equal SCSA 'ab-color)
	 (funcall *selected-function* board '(A B) SCSA last-response))
	(T
	 (funcall *selected-function* board colors SCSA last-response))))

;;; **************************************
;;; BASELINES
;;; **************************************

;;;BASELINE 1: brute force.
;;;Exhaustively enumerate all possibilities. Guess each possibility in lexicographic order one at a time.
;;;code snippet reference: https://github.com/Lambdaah/AI-Mastermind/blob/master/Mastermind%20for%20students.lisp

; *combinations* - Holds a list of all combinations from colors of size 'board'.
; *guess* - Holds a list of all possible variations of combinations.
             ;In other words, permulate each element in *combinations* and save them to *guess*.
             ;cardinality of *guess* is bigger than cardinality of *combinations*

;;Exhaustively enumerates all possibilities, paying no attention to SCSA.
;;Only use 'last-responses = nil' for initialization. Paying no attention to last-response after initialization. 
(defun baseline-1-Dino (board colors SCSA last-response)
  (declare (ignore SCSA))
  (cond (last-response nil)
        ((setf *combinations* (combination colors board));set *combinations* to all possible combinations from colors of size 'board'. 
         (permofperm *combinations*);get the list(*guess*) of permutations of each element in *combinations* 
         (setf *guess* (remove-duplicates *guess* :test #'equal)))
        (T (setf *guess* (remove-duplicates *guess* :test #'equal)))); remove dupicates from *guess* to generate our final guess.
  (pop *guess*)) 

;;gets all possible combinations with repetitions computed from a set colors of a fixed size board.
;;compute the ways we can chose a fix number(board is the number in this case) of colors from a set of colors
;;k-combination with repetitions: https://en.wikipedia.org/wiki/Combination
;;code snippet reference: https://rosettacode.org/wiki/Combinations_with_repetitions#Common_Lisp
(defun combination (colors board)  
  (let ((first-color (first colors)))
    (cond ((null colors) nil)
          ((= board 1) (mapcar #'list colors))
          (t (append (mapcar (lambda (colors) (cons first-color colors))
            (combination colors (- board 1)))
            (combination (rest colors) board))))))

;; permutations of permutation, creates a new list with all possible variations
(defun permofperm (combinations)
(loop for i in combinations
  do (loop for j in (all-permutations i)
    do (push j *guess*))))  

;; get all possible permutations of a list without duplicates, but without all variations in each position
;; all permutations of a list L is: for each element E in L , that element prepended to all permutations of 
;; [ L with E removed ]
;; code snippet reference: https://stackoverflow.com/questions/2087693/how-can-i-get-all-possible-permutations-of-a-list-with-common-lisp
(defun all-permutations (lst &optional (remain lst))
  (cond ((null remain) nil)
        ((null (rest lst)) (list lst))
        (t (append (mapcar (lambda (l) (cons (first lst) l))
           (all-permutations (rest lst)))
           (all-permutations (append (rest lst) (list (first lst))) (rest remain))))))

;;;BASELINE 2
;;;Brute force but eliminate the colors for which getting response of (0,0)
;;;code snippet reference: https://github.com/Lambdaah/AI-Mastermind/blob/master/Mastermind%20for%20students.lisp

;*avoid-colors* - Stores list of colors which should be avoided. 
;*permutations* - Holds list of all possible permutations generated from colors of size board.
;*guess* - Stores guess.
;*position* - Position while we are parsing through permutations

;;Exhaustively enumerates all possibilities, paying no attention to SCSA.
;;Use 'last-responses = nil' for initialization. Response to last-response when getting (0,0)
(defun baseline-2-Dino (board colors SCSA last-response)
  (declare (ignore SCSA))
  (cond ((equal last-response nil)
         (setf *avoid-colors* nil)
         (setf *position* 1)
         (setf *permutations* (k-permutations colors board))
         (setf *guess* (first *permutations*)))
	((= (+ (first last-response) (second last-response)) 0)
	 (update-avoids)
	 (setf *guess* (get-next-guess)))
	(T (setf *guess* (get-next-guess))))
   *guess*)

;;Helper function creates all possible k length permutations
;;Code snipped reference https://gist.github.com/capablemonkey/f824aeed72efe007078abb235ac8d22a
(defun k-permutations (n-list k)
  (cond ((= 0 k) (list nil))
	((null n-list) nil)
	((null (rest n-list)) (list n-list))
	(t (loop for element in n-list
	    append (mapcar (lambda (l) (cons element l))
	    (k-permutations n-list (- k 1)))))))

;;Helper function for updating colors which we should be avoiding
(defun update-avoids ()
  (setf *guess* (remove-duplicates *guess*))
  (loop for i from 0 to (- (length *guess*) 1)
    do (push (nth i *guess*) *avoid-colors*)))

;;Helper function return the next guess from *permutations*
(defun get-next-guess ()
  (let ((newcode (nth *position* *permutations*))
        (i 0))
    (incf *position*)
    (loop while (< i (length *avoid-colors*))
    do (cond 
        ((member (nth i *avoid-colors*) newcode)
         (setf newcode (nth *position* *permutations*))
         (incf *position*)
         (setf i 0))
        (T (incf i))))
    newcode))

;;;BASELINE 3
;*quantities* - stores quantities of each color

(defun baseline-3-Dino (board colors SCSA last-response)
					; last response is a list containing (correct-pos, correct-color, num-guesses)
  (declare (ignore SCSA))
  (cond ((null last-response) ;if this is the first guess, initialize quantities to all zeros, guess all color 1
	 (setf *guess* (make-list board :initial-element (first colors)))
	 (setf *quantities* (make-list (list-length colors) :initial-element 0))
	 (return-from baseline-3-Dino *guess*))
	((< (third last-response)  (- (list-length colors) 1)) ;if number of guesses < number of colors guess all the next color 
	 (setf (nth (- (third last-response) 1) *quantities*) (first last-response))
	 (setf *guess* (make-list board :initial-element (nth (third last-response) colors)))
	 (return-from baseline-3-Dino *guess*))
	((= (third last-response) (- (list-length colors) 1)) ;if all but one of the colors have been guessed, calculate values for last color and generate the first valid guess with the discovered color distribution
	 (setf (nth (- (third last-response) 1) *quantities*) (first last-response))
	 (setf (nth (third last-response) *quantities*) (- board (apply '+ *quantities*))) ;subtract sum so far from total number of pegs to get number of pegs for last color
	 (setf *guess* (generate-with-distribution colors *quantities* NIL)))
	(T ;using the last guess and Knuth's permutation algorithm, generate the next valid guess for the discovered color distribution
	 (setf *guess* (generate-with-distribution colors *quantities* *guess*))
	 
	 (return-from baseline-3-Dino *guess*))))

; uses last guess to generate the next permutation of that guess.
; Makes use of Donald E. Knuth's Algorithm L 
; References:
; Knuth, D. "Generating All Combinations", Stanford University
					; http://www.kcats.org/csci/464/doc/knuth/fascicles/fasc3a.pdf
; Python Example of Algorithm L by rocksportrocker on StackOverflow:
					; https://stackoverflow.com/questions/361/generate-list-of-all-possible-permutations-of-a-string
(defun generate-with-distribution (colors distrib last-guess)
  (cond
    ((null last-guess)
      (loop for i from 0 to (- (list-length colors) 1) ;if called with last-guess = NIL, generate the first guess using the distribution
	 append (make-list (nth i distrib) :initial-element (nth i colors)) into first-guess ;make a list with colors in order
	 finally (return first-guess)))
    (T
     (let ((indices (generate-helper2 last-guess (generate-helper last-guess))) (new-guess (copy-list last-guess))) ;else
       (rotatef (nth (first indices) new-guess) (nth (second indices) new-guess))
       (return-from generate-with-distribution (append (subseq new-guess 0 (+ (first indices) 1)) (reverse (subseq new-guess (+ (first indices) 1)))))))))

(defun generate-helper (last-guess) ;finds k0 for Knuth permutation algorithm
  (loop for i from 0 to (- (list-length last-guess) 2) 
     if (> (spot (nth (+ i 1) last-guess)) (spot (nth i last-guess)))
       maximize i into k0
     finally (return-from generate-helper (list k0 (+ k0 1)))))

(defun generate-helper2 (last-guess indices)  ;finds l0 for Knuth permutation algorithm
  (loop for i from (+ 1 (first indices)) to (- (list-length last-guess) 1) 
     if (> (spot (nth i last-guess)) (spot (nth (first indices) last-guess)))
       maximize i into l0
     finally (return-from generate-helper2 (list (first indices) l0))))

;;;BASELINE 4
; Variables: *inferences*, *gameover*, *N*, *G*, *beingfixed*, *beingconsidered*, *colors*, *bulls*, *cows*, *gain*, totalnum, tempnum

;; References:
;; 	Rao, T. Mahadeva. "An Algorithm to Play the Game of Mastermind", SUNY College at Brockport Brockport, NY 14420

(defun baseline-4-Dino (board color SCSA last-response)
  (declare (ignore SCSA))
  (setf *N* board)
  (setf *colors* color)
  ;;Set bulls and cows
  (cond ((null last-response) (setf *bulls* 0) (setf *cows* 0))
	(T (setf *bulls* (first last-response)) (setf *cows* (second last-response))))
  ;;build guess
  (cond ((null last-response) (setf *gameover* nil) (setup board color) *G*)
	((and (<= (first last-response) *N*) (null *gameover*)) (Update) (Getnext) (if (= *bulls* *N*) (setf *gameover* 'T))*G*)
	(*gameover* *G*)
	(T *G*)))


;;return the first items in top level in *inferences* 
(defun getlist ()
  (loop for i from 1 to (length *inferences*)
     for item in *inferences*
     collect (first item) into x
     finally (return x)))


;;initialize variables and guess
(defun setup (board color)
  (loop for i from 0 to (- board 1)
     collect (first color) into x
     finally (setf *G* x))
  (setf *beingfixed* 0) 
  (setf *beingconsidered* (first color)) 
  (setf *inferences* nil)
  (setf *gameover* nil))

;;Tied(i)boolean; Return true if the position of i has color tied to it.
(defun Tied (i) 
  (loop for item in *inferences*
     when (and (= (length (second item)) 1) (equal i (first (second item))))
     do (return T)))
;;Itscolor(i) : colors; when i is a tied position returns the color to which i is tied. 
(defun Itscolor (i) 
  (loop for item in *inferences*
     when (and (= (length (second item)) 1) (equal i (first (second item))))
     do (return (first item))))
;;Nextpos(i) : positions; Returns the next possible position for color i. That is, if i=3 and the corresponding sublist is (3(2 4 5)) then it returns 2. 
(defun Nextpos (i)
  (loop for item in *inferences*
     when (and (equal i (first item)) (> (length (second item)) 1))
     do (return (first (second item)))))
;;Secondunfixed(inferences) : colors; Returns the second color which is not yet fixed 
(defun Secondunfixed (inferences)
  (loop for item in inferences
     if (> (length (second item)) 1) 
		if(not (equal (first item) *beingfixed*))
			do(return (first item))
	finally(return *beingfixed*)))
	 
 ;;build guess
(defun Getnext ()
  (if (and (equal *beingconsidered* *beingfixed*) (not (equal (Secondunfixed *inferences*) *beingconsidered*)))
      (NextColor *beingconsidered*))
  (loop for i from 0 to (- *N* 1)
     if (equal (Tied i) T) 
     do (setf (nth i *G*) (Itscolor i))
     else if(equal i (Nextpos *beingfixed*))
     do (setf (nth i *G*) *beingfixed*)
     else if (= (length *inferences*) *N*)
     do (setf (nth i *G*) (Secondunfixed *inferences*))
     else do (setf (nth i *G*) *beingconsidered*)))

;;Addlists(gain, beingconsidered, inferences)
;;Adds sublists (equal in number to gain) to the list inferences each sublist with header 'beingconsidered'. 			
(defun Addlists(gain beingconsidered)
  (if (>= (length *inferences*) *N*)
      ()
	(loop for i from 0 to gain
	   when (< 0 i)
	   do (loop for i from 0 to (- *N* 1)
		 collect i into sublist
		 finally (setf *inferences* (append *inferences* (list(list beingconsidered sublist))))))))

;;Fix(beingfixed)
;;'Fix'es the beingfixed in its next possible position and deletes appropriate position from other lists. 
(defun Fix(beingfixed)
  (loop for item in *inferences*
     when (and (equal (first item) beingfixed) (> (length (second item)) 1))
     do (progn
	  (setf (second item) (list(first (second item))))
	  (loop for position in *inferences*
	     when (> (length (second position)) 1)
	     do (setf (second position) (remove (first (second item)) (second position))))
	  (return *inferences*))))
	  
;;Bump(beingfixed)
;; BeingFixed will get an updated value. 	
(defun Bump()
  (if (and (equal *beingfixed* 0) (not(null( first (getlist)))))
      (setf *beingfixed* (first (getlist)))
	(loop for item in *inferences*
		if (> (length (second item)) 1)
			do(return(setf *beingfixed* (first item))))))

;;Deletes the current position of the color i form the sublist for color j	  
(defun Del(i j)
  (loop for item in *inferences*
     if (and (equal i (first item)) (> (length (second item)) 1))
	   collect (second item) into x
	   finally (loop for position in *inferences*
				 if (and (> (length (second position)) 1)(equal j (first position)))
					do (setf (second position) (remove (first (first x)) (second position))))))

;;fixes the color i in the current position of the color j
(defun Fix1(i j)
      (loop for item in *inferences*
	 when (and (equal (first item) j) (> (length (second item)) 1))
		collect (second item) into x
		finally(loop for position in *inferences*
	       if (and (equal (first position) i) (> (length (second position)) 1))
	       do (return (setf (second position) (list(first (first x))))))))
		   
;;cleans up the inferences list
(defun Cleanup()
  (loop for item in *inferences*
     when (= (length (second item)) 1)
     do (loop for position in *inferences*
	   when (> (length (second position)) 1)
	   do(setf (second position) (remove (first (second item)) (second position))))))

;;Nextcolor(beingconsidered) : Gets a new color for being considered.
(defun NextColor(beingconsidered)
  (if (not (null (first (rest (member beingconsidered *colors*)))))
      (setf *beingconsidered* (first (rest (member beingconsidered *colors*))))
      (setf *beingconsidered* 0)))
  
;;returns the number of colors in guess that has a positions inferences.
(defun Numfix (inferences)
  (declare (ignore inferences))
  (setf totalnum 0)
  (loop for i in (remove-duplicates *G*)
     do (progn
	  (setf tempnum totalnum)
	  (setf totalnum (+ (min (count i *G*) (count i (getlist))) tempnum)))
     finally (return totalnum)))

;;Updates Inferences
(defun Update()
  (setf *gain* (-(+ *bulls* *cows*) (Numfix *inferences*)))
  (Addlists *gain* *beingconsidered*)
  (case *cows*
    ((0) (progn (Fix *beingfixed*)))
    ((1) (progn (if(equal 0 *beingconsidered*) 
					(Del *beingfixed* (Secondunfixed *inferences*))
					(Del *beingfixed* *beingconsidered*))
				(Del *beingfixed* *beingfixed*)))
    ((2) (progn (if(equal 0 *beingconsidered*)
					(Fix1 (Secondunfixed *inferences*) *beingfixed*) 
					(Fix1 *beingconsidered* *beingfixed*)))))
  (Bump)  
  (Cleanup)
  (Nextcolor *beingconsidered*))

;;; **************************************
;;; SCSA FUNCTIONS
;;; **************************************

;;First and Last is based on Baseline-4-Dino
;;When the first color or the last color is found, set the both color to the two position, if haven't done so already.
;;This is improve the guess by at most one guess from Baseline-4-Dino. 
;;It will not improve guess if the first and last color is the last color in the color list.
(defun dino-first-and-last (board color SCSA last-response)
  (declare (ignore SCSA))
  (setf *N* board)
  (setf *colors* color)
  ;;Set bulls and cows
  (cond ((null last-response) (setf *bulls* 0) (setf *cows* 0))
	(T (setf *bulls* (first last-response)) (setf *cows* (second last-response))))
  ;;build guess
  (cond ((null last-response) (setf *gameover* nil) (setup board color) *G*)
	((and (<= (first last-response) *N*) (null *gameover*)) (Update) (FirstLastGetNext) (if (= *bulls* *N*) (setf *gameover* 'T))*G*)
	(*gameover* *G*)
	(T *G*)))

;;helper function that sets the first or last position of a color.
(defun setFirstOrLastPosition(color)
	(loop for item in *inferences*
		when (and (> (length (second item)) 1) (not (null (member (- *N* 1) (second item)))) (equal color (first item)))
		do(return(setf (second item) (list (- *N* 1))))))
		
;;build first and last
(defun FirstLastGetNext ()
 (if (and (equal (Tied (- *N* 1)) nil) (equal (Tied 0) T))
	(progn
	(setFirstOrLastPosition (Itscolor 0))
	(Bump)))
 (Getnext))

;;;TWO-COLOR-ALTERNATING
(defun dino-two-color-alternating (board colors SCSA last-response)
					; last response is a list containing (correct-pos, correct-color, num-guesses)
  (declare (ignore SCSA))
  ;(format t "~%last guess:")(print *last-guess*)     
  ;(format t "~%quantities:")(print *quantities*)	
  ;(format t "~%num of guesses:")(print last-response)  
  (cond ((null last-response) ;if this is the first guess, initialize quantities to all zeros, guess all color 1
	 (setf *last-guess* (make-list board :initial-element (first colors)))
	 (setf *quantities* (make-list (list-length colors) :initial-element 0))
         (setf *two-colors* NIL)
	 (return-from dino-two-color-alternating *last-guess*))
        ((< (third last-response)  (- (list-length colors) 1)) ;if number of guesses < number of colors guess all the next color 
	 (setf (nth (- (third last-response) 1) *quantities*) (first last-response))
	 (setf *last-guess* (make-list board :initial-element (nth (third last-response) colors)))
	 (return-from dino-two-color-alternating *last-guess*))
        ((= (third last-response) (- (length colors) 1)) ;if all but one of the colors have been guessed, 
         ;calculate values for last color 
         ;and generate the first valid guess with the discovered color distribution
	 (setf (nth (- (third last-response) 1) *quantities*) (first last-response))
	 (setf (nth (third last-response) *quantities*) (- board (apply '+ *quantities*))) ;subtract sum so far from total number of pegs 
         ;to get number of pegs for last color
         (find-two-colors *quantities* colors)
	 (setf *last-guess* (try-two-colors-alternating board *two-colors* NIL)))
	(T  
	 (setf *last-guess* (try-two-colors-alternating board *two-colors* *last-guess*))
	 (return-from dino-two-color-alternating *last-guess*))))

;;find two colors from *quantities* 
(defun find-two-colors(*quantities* colors)
  (loop for i from 0 to (- (length *quantities*) 1) 
    do (when (/= 0 (nth i *quantities*)) 
    (push (nth i colors) *two-colors*)))
  ;(format t "~%two colors:")(print *two-colors*)
)

;;set guess with two color alternating 
(defun try-two-colors-alternating (board *two-colors* last-guess)
  (cond((null last-guess)
    (loop with first-color = (first *two-colors*)
     with second-color = (second *two-colors*)
      for i from 1 to board
      when (oddp i) 
      collect first-color
      else collect second-color))
   (T
    (loop with first-color = (first *two-colors*)
     with second-color = (second *two-colors*)
     for i from 1 to board
     when (evenp i) 
     collect first-color
     else collect second-color))))

;;;*******************************************************************************************
;;FUNCTIONS NOT IN USE
;;;*******************************************************************************************
;;; including dino-ab-color, dino-only-once, dino-mystery2, and the general solver dino-local-search
;;; These functions were removed because baseline-4 outperformed them on the task they were designed for.

;;; AB-COLORS
(defun dino-ab-color (board colors SCSA last-response)
					; last response is a list containing (correct-pos, correct-color, num-guesses)
  (declare (ignore colors SCSA))
  (cond ((null last-response) ;if this is the first guess, initialize quantities to all zeros, guess all color 1
	 (setf *last-guess* (make-list board :initial-element (first *abcolors*)))
         (setf *quantities* (make-list (list-length *abcolors*) :initial-element 0))
	 (return-from dino-ab-color *last-guess*))
        ((< (third last-response)  (- (list-length *abcolors*) 1)) ;if number of guesses < number of colors guess all the next color 
	 (setf (nth (- (third last-response) 1) *quantities*) (first last-response))
	 (setf *last-guess* (make-list board :initial-element (nth (third last-response) *abcolors*)))
	 (return-from dino-ab-color *last-guess*))
	((= (third last-response) (- (list-length *abcolors*) 1)) ;if all but one of the colors have been guessed, 
         ;calculate values for last color 
         ;and generate the first valid guess with the discovered color distribution
         (setf (nth (- (third last-response) 1) *quantities*) (first last-response))
	 ;(setf (nth (third last-response) *quantities*) (first last-response))
	 (setf (nth (third last-response) *quantities*) (- board (apply '+ *quantities*))) ;subtract sum so far from total number of pegs 
         ;to get number of pegs for last color
	 (setf *last-guess* (generate-with-abcolors *abcolors* *quantities* NIL)))

	(T ;using the last guess and Knuth's permutation algorithm, generate the next valid guess for the discovered color distribution
	 (setf *last-guess* (generate-with-abcolors *abcolors* *quantities* *last-guess*))
	 (return-from dino-ab-color *last-guess*))))

; uses last guess to generate the next permutation of that guess.
; Makes use of Donald E. Knuth's Algorithm L 
; References:
; Knuth, D. "Generating All Combinations", Stanford University
					; http://www.kcats.org/csci/464/doc/knuth/fascicles/fasc3a.pdf
; Python Example of Algorithm L by rocksportrocker on StackOverflow:
					; https://stackoverflow.com/questions/361/generate-list-of-all-possible-permutations-of-a-string
(defun generate-with-abcolors (*abcolors* distrib last-guess)
  (cond ((null last-guess) 
         (loop for i from 0 to (- (list-length *abcolors*) 1) ;if called with last-guess = NIL, generate the first guess using the distribution
	 append (make-list (nth i distrib) :initial-element (nth i *abcolors*)) into first-guess
        ;make a list with colors in order
	 finally (return first-guess)))
        (T
         (let ((indices (generate-helper2 last-guess (generate-helper last-guess))) (new-guess (copy-list last-guess))) ;else
           (rotatef (nth (first indices) new-guess) (nth (second indices) new-guess))
           (return-from generate-with-abcolors (append (subseq new-guess 0 (+ (first indices) 1)) (reverse (subseq new-guess (+ (first indices) 1)))))))))

;; MYSTERY 2
;;I assume that mystery-2 is like three color alternating
;;format of mystery-2 is A B C A B C A where A, B, C are unique color.
;;A is first_color
;;B is second_color
;;C is third_color


;;Support functions for dino-mystery-2
;;reset bulls and cows to 0
;;set guess to all of the first color
;;initialize neccessary variables for mystery-2
(defun mystery2initialize ()
  (loop for i from 0 to (- *numOfPos* 1)
     collect (first *colors*) into x
     finally (setf *guess* x))
  (setf *bulls* 0) 
  (setf *cows* 0)
  (setf *numOfGuesses* 0)
  (setf *first_color* nil)
  (setf *second_color* nil)
  (setf *third_color* nil)
  (setf *color_list* nil)
  (setf *correctColorPos* -1)
  (setf *correct_first_color* nil)
  (setf *correct_second_color* nil)
  (setf *correct_third_color* nil)
  (setf *curColorPos* 0)
  (setf *nonColor* nil)
  (setf *testIfCorrectAlgorithm* nil)
  (setf *correctAlgorithm* nil)
  (setf *needpermutation* nil)
  (setf *permutationPos* 0)
  (setf *permutationList* nil))

;;------------Functions to find the three colors-----------	  	
;;Find the color using bulls and also find a non used color, which is then later used in mystery2postTestBuild
(defun mystery2preTestUpdate()
  (if (< 0 *bulls*)
      (mystery2updateColor (nth *curColorPos* *colors*)))
  (if (and (null *nonColor*) (= 0 (+ *cows* *bulls*)))
      (setf *nonColor* (nth *curColorPos* *colors*))))
	  
;;Update first_color, second_color, and third_color when founded
(defun mystery2updateColor (color)
  (cond ((null *first_color*) (setf *first_color* color))
	((null *second_color*) (setf *second_color* color))
	((null *third_color*) (setf *third_color* color))))
	  
;;Set the next color to find
(defun mystery2GetNext()
  (setf *curColorPos* (+ *curColorPos* 1)))
  
;;Set guess to all of the same color where the color have not been used yet
(defun mystery2premystery2testBuild ()
  (loop for i from 0 to (- *numOfPos* 1)
     collect (nth *curColorPos* *colors*) into x
     finally (setf *guess* x)))

;;------------Function to find out if the Algorithm works-----------	  
;;set guess with all three colors alternating
(defun mystery2testBuild ()
  (setf *color_list* (list *first_color* *second_color* *third_color*))
  (setf *correctColorPos* 0)
  (setf firstColor T)
  (setf secondColor nil)
  (setf thirdColor nil)
  (loop for i from 0 to (- *numOfPos* 1)
     do(cond (firstColor (setf (nth i *guess*) *first_color*) (setf firstColor nil) (setf secondColor T))
	     (secondColor (setf (nth i *guess*) *second_color*) (setf secondColor nil) (setf thirdColor T))
	     (thirdColor (setf (nth i *guess*) *third_color*) (setf thirdColor nil) (setf firstColor T)))))
		 
;;check to see if the sum of bulls and cows are close to the number of position
;;e.g with a board of 6,7, or 8, then the sum of bulls and cows must be greater than 6 and less than 9
;;likewise, with a board of 9, 10 or 11, then the sum of bulls and cows must be greater than 9 and less than 12
(defun mystery2checkIfCorrect ()
  (cond ((and (<= (- *numOfPos* (rem *numOfPos* 3)) (+ *bulls* *cows*))
          (> (+ (- *numOfPos* (rem *numOfPos* 3))3) (+ *bulls* *cows*))) (setf *correctAlgorithm* T) (mystery2findCorrectPos) *guess*)
	(T (print "Algorithm does not work"))))

;;-----------Functions after finding that this Algorithm works-----------
;;Find the correct position for the color using bulls
(defun mystery2postTestUpdate ()
  (if (< 0 *bulls*)
      (mystery2updateCorrectColor (nth *correctColorPos* *color_list*))))
	  
;;Update the position for the color
(defun mystery2updateCorrectColor (color)
  (cond ((null *correct_first_color*) (setf *correct_first_color* color))
	((null *correct_second_color*) (setf *correct_second_color* color))
	((null *correct_third_color*) (setf *correct_third_color* color)))
  (setf *color_list* (remove color *color_list*)))

;;This is where guess is being made
;;Depending on the length of colors
;;If there is exactly 3 colors to being with then use permutation
;;Otherwise find the correct position for the color e.g first second or third
(defun mystery2findCorrectPos ()
  (mystery2postTestBuild)
  (if (not *needpermutation*)
      (progn 
	(setf *correctColorPos* (+ 1 *correctColorPos*))
	(if (> *correctColorPos* (- (length *color_list*) 1))
	    (setf *correctColorPos* 0))
	
	(cond ((null *correct_first_color*) (setf (first *guess*) (nth *correctColorPos* *color_list*)))
	      ((null *correct_second_color*) (setf (second *guess*) (nth *correctColorPos* *color_list*)))
	      ((null *correct_third_color*) (mystery2updateCorrectColor (nth *correctColorPos* *color_list*)) (mystery2Build))))
      (progn
	(if (null *permutationList*)
	    (progn
	      (mystery2makepermutationList)
	      (setf *permutationPos* 0))
	    (progn
	      (setf *guess* (nth *permutationPos* *permutationList*))
	      (setf *permutationPos* (+ 1 *permutationPos*)))))))
		  
;;Determine whether to use permutation or check for correct color position 
(defun mystery2postTestBuild ()
  (if (and (null *nonColor*) (> (- (length *colors*) 1) *curColorPos*))
      (setf *nonColor* (nth (+ *curColorPos* 1) *colors*)))
  (if (not (null *nonColor*))
					;We can test and find which is the correct first, second, and third color
      (progn 
	(loop for i from 0 to (- *numOfPos* 1)
	   collect *nonColor* into x
	   finally (setf *guess* x)))
					;Cannot Test so use permutation to find out
      (setf *needpermutation* T)))

;;set guess to the correct guess
(defun mystery2Build ()
  (setf firstColor T)
  (setf secondColor nil)
  (setf thirdColor nil)
  (loop for i from 0 to (- *numOfPos* 1)
     do(cond (firstColor (setf (nth i *guess*) *correct_first_color*) (setf firstColor nil) (setf secondColor T))
	     (secondColor (setf (nth i *guess*) *correct_second_color*) (setf secondColor nil) (setf thirdColor T))
	     (thirdColor (setf (nth i *guess*) *correct_third_color*) (setf thirdColor nil) (setf firstColor T)))))
		 
;;-----------Functions for permutation-----------
;;create a permutation list with the three color
(defun mystery2makepermutationList()
  (setf *color_list* (list *first_color* *second_color* *third_color*))
  (loop for x from 0 to 2		
     do(loop for y from 0 to 1 
	  do(setf color2 (remove (nth x *color_list*) *color_list*))
	  do(setf color3 (remove (nth y color2) color2))
	  do(mystery2permutationBuild (nth x *color_list*) (nth y color2) (first color3)))))

;;create a premutated guess and append it to the permutation list
(defun mystery2permutationBuild (Color1 Color2 Color3)
  (setf firstColor T)
  (setf secondColor nil)
  (setf thirdColor nil)
  (loop for i from 0 to (- *numOfPos* 1)
     if firstColor
     collect Color1 into permutation
     and do(progn 
	     (setf firstColor nil) 
	     (setf secondColor T))
     else if secondColor
     collect Color2 into permutation 
     and do(progn 
	 (setf secondColor nil) 
	 (setf thirdColor T))
     else if thirdColor
     collect Color3 into permutation
     and do(progn 
	 (setf thirdColor nil) 
	 (setf firstColor T))
     finally(progn
	      (setf *permutationList* (append *permutationList* (list permutation))))))

		  

;;Support functions for dino-only-once

;;OnlyOnceinitialize - reset bulls and cows and guess will be all of the first color
(defun OnlyOnceinitialize ()
  (loop for i from 0 to (- *numOfPos* 1)
     collect (first *colors*) into x
     finally (setf *guess* x))
  (setf *bulls* 0) 
  (setf *cows* 0)
  (setf *numOfGuesses* 0)
  (setf *correctColors* nil)
  (setf *correctColorsWithPosition* nil)
  (setf *correctColorPos* 0)
  (if (= (length *colors*) *numOfPos*)
      (progn
	(setf *correctColors* *colors*)
	(setf *curColorPos* 1)
	(OnlyOnceFindCorrectColorPosition))
      (setf *curColorPos* 0)))

;;-----------------Functions to find the correct colors----------------------
;;Find the color using bulls 
;;After finding the last color, then call OnlyOnceCorrectColorsWithPositionUpdate
(defun OnlyOnceCorrectColorsUpdate ()
  (if (< 0 *bulls*)
      (setf *correctColors* (append *correctColors* (list (nth *curColorPos* *colors*)))))
  (if (= (length *correctColors*) *numOfPos*)
      (progn
	(setf *curColorPos* 1)
	(OnlyOnceFindCorrectColorPosition));Find correctColorPos
      (progn
	(setf *curColorPos* (+ 1 *curColorPos*))
	(OnlyOnceGetNext))))
;;Set the guess to all of the same color that is not found yet
(defun OnlyOnceGetNext()
  (loop for i from 0 to (- *numOfPos* 1)
     collect (nth *curColorPos* *colors*) into x
     finally (setf *guess* x)))

;;------------------Functions to find the correct position for each color-------------
;;Set the guess to all of the same color that does not have a position yet
(defun OnlyOnceGetNext2()
  (loop for i from 0 to (- *numOfPos* 1)
     collect (nth *curColorPos* *correctColors*) into x
     finally (setf *guess* x)))

;;Determine the position of each color
(defun OnlyOnceFindCorrectColorPosition()
  (if (= (length *correctColorsWithPosition*) *numOfPos*)
      (setf *guess* *correctColorsWithPosition*)
      (progn
	(OnlyOnceGetNext2)
	(setf (nth (length *correctColorsWithPosition*) *guess*) (nth *correctColorPos* *correctColors*)))))

;;Update the position of a color when found
(defun OnlyOnceCorrectColorsWithPositionUpdate()
  (if (= 2 *cows*) ;Both Color are in the wrong position so we swap them
      (progn
	(setf *correctColorsWithPosition* (append *correctColorsWithPosition* (list(nth *curColorPos* *correctColors*))))
	(setf *correctColors* (remove (nth *curColorPos* *correctColors*) *correctColors*))
	(if (= (length *correctColors*) 1)
	    (setf *correctColorsWithPosition* (append *correctColorsWithPosition* *correctColors*)))
	(setf *correctColorPos* 0)
	(setf *curColorPos* 1)
	))
  (if (= 0 *cows*) ;the Color are in the correct position so we add it to that position
       (progn
	(setf *correctColorsWithPosition* (append *correctColorsWithPosition* (list(nth *correctColorPos* *correctColors*))))
	(setf *correctColors* (remove (nth *correctColorPos* *correctColors*) *correctColors*))
	(if (= (length *correctColors*) 1)
	    (setf *correctColorsWithPosition* (append *correctColorsWithPosition* *correctColors*)))
	(setf *correctColorPos* 0)
	(setf *curColorPos* 1)
	))
  (if (= 1 *cows*) ;Color is in the wrong position we go to next color
      (progn
	(setf *correctColorPos* (+ 1 *correctColorPos*))
	(if (< (length *correctColors*) *correctColorPos*)
	    (setf *correctColorPos* 0))
	(if (= *correctColorPos* *curColorPos*)
	    (setf *curColorPos* (+ 1 *curColorPos*)))
	(if (< (length *correctColors*) *curColorPos*)
	    (setf *curColorPos* 0)))))


;;main SCSA based functions
(defun dino-mystery-2 (board color SCSA last-response)
  (declare (ignore SCSA))
  (setf *numOfPos* board)
  (setf *colors* color)
  (cond ((null last-response) (mystery2initialize)) ;If first guess then initialize variables.
	(T (setf *bulls* (first last-response))	;else set bulls, cows, and number of guess made so far
	   (setf *cows* (second last-response))
	   (setf *numOfGuesses* (third last-response))))
	  
	;;color must have more than 3 colors
	(if (< (length color) 3)
		(print '(This does not support less than 3 colors)))
	
	;;if length of color is 3 then we know all three colors
   (if (and (= (length color) 3) (null *first_color*)) 
	(progn
		(setf *first_color* (first color))
		(setf *second_color* (second color))
		(setf *third_color* (third color))))
	   
  (cond ((null last-response) *guess*) ;guess will be all of the first color
	((= *bulls* *numOfPos*) *guess*) ;finished guessing
	((and *testIfCorrectAlgorithm* (null *correctAlgorithm*))(mystery2checkIfCorrect));After finding out all three color check if the algorithm is correct
	((null *third_color*) ;find all three colors
	 (mystery2preTestUpdate) ;Using Bulls to determine if it is one of the three colors
	 (if (null *third_color*) ;Have not found the last color
	     (progn
	       (mystery2GetNext) ;Choose next color
	       (mystery2premystery2testBuild) ;build guess
	       *guess*)
	     (progn
	       (setf *testIfCorrectAlgorithm* T) ;If third color is found then going to Testing phrase
	       (mystery2testBuild) ;build guess with all three colors alternating
	       *guess*)))
	((and *third_color* (null *testIfCorrectAlgorithm*)) (setf *testIfCorrectAlgorithm* T) (mystery2testBuild) *guess*) ;Testing phrase
	((null *correct_third_color*) (mystery2postTestUpdate) (mystery2findCorrectPos) *guess*) ;Determine the correct Position of each color
	(T (mystery2Build) *guess*)))

(defun dino-only-once (board color SCSA last-response)
  (declare (ignore SCSA))
  (setf *numOfPos* board)
  (setf *colors* color)
  (cond ((null last-response) (OnlyOnceinitialize)) ;If first guess then initialize guess.
	(T (setf *bulls* (first last-response))	;else set bulls, cows, and number of guess made so far
	   (setf *cows* (second last-response))
	   (setf *numOfGuesses* (third last-response))))
  
  (cond ((null last-response) *guess*) ;guess will be all of the first color
	;;Find the correct colors
	((not (= (+ (length *correctColors*)(length *correctColorsWithPosition*)) board))
	 (OnlyOnceCorrectColorsUpdate)
	 *guess*)
	 ;;All colors matches 
	((= (length *correctColorsWithPosition*) board) *correctColorsWithPosition*)
	;;Find the correct position for each color
	((= (+ (length *correctColors*)(length *correctColorsWithPosition*)) board)
	 (OnlyOnceCorrectColorsWithPositionUpdate)
	 (OnlyOnceFindCorrectColorPosition)
	 *guess*)
	(T *guess*)))

;;; **************************************
;;;LOCAL SEARCH - baseline3 combined with a local search.
;;; **************************************

; *found-colors* - set to true once distribution of colors is found
; *prepared* -  set to true once preparations are over (once *candidates* reaches *beam-width* for the first time)
; *guess-index* - index of the last memeber of candidates a successor was generated from
; *candidates* - stores list of lists each containing a guess and the number of correct position of pins in that guess. form: ((guess-1 correctpins-1) ... (guess-n correctpins-n)
; *already-guessed* - stores list of previous guesses. form (guess-1 guess-2 ... guess-n)
; *known-pegs* - stores one correct peg in each position or NIL if correct peg for that position is unknown.
; *wrong-pegs* - stores a list of wrong pegs in each position or NIL
; *last-i* - stores one of the two indices (i) modified last time a successor was generated
; *last-j* - stores one of the two indices (j) modified last time a successor was generated
(defparameter *beam-width* 1) ;initial number of candidates, max. number of candidates is beam-width*2
(defparameter *epsilon* 50) ;there's a 1/epsilon chance to make a non-optimal swap

(defun dino-local-search (board colors SCSA last-response)
					; last response is a list containing (correct-pos, correct-color, num-guesses)
  (declare (ignore SCSA))
  (cond ((null last-response) ;if this is the first guess, initialize quantities to all zeros, guess all color 1. Also initialize all variables.
	 (setf *guess* (make-list board :initial-element (first colors)))
	 (setf *quantities* (make-list (list-length colors) :initial-element 0))
	 (setf *found-colors* NIL)
	 (setf *prepared* NIL)
	 (setf *guess-index* -1)
	 (setf *candidates* NIL)
	 (setf *already-guessed* NIL)
	 (setf *known-pegs* (make-list board :initial-element NIL))
	 (setf *wrong-pegs* (make-list board :initial-element NIL))
	 (setf *last-i*  NIL)
	 (setf *last-j*  NIL)
	 (return-from dino-local-search *guess*))
	((and (< (third last-response)  (- (list-length colors) 1)) (not *found-colors*)) ;if number of guesses < number of colors and we haven't found all colors in the code
	 (setf (nth (- (third last-response) 1) *quantities*) (first last-response))
	 (cond ((equal (apply '+ *quantities*) board) ;if number of pegs whose colors we know = number of pegs, generate the first valid guess with the discovered color distribution
		(setf *found-colors* T)
		(setf *guess* (generate-with-distribution colors *quantities* NIL))
		(setf *candidates* (append *candidates* (list *guess*)))
		(setf *already-guessed* (append *already-guessed* (list *guess*))))
	       (T   ;otherwise, guess all the next color
		(setf *guess* (make-list board :initial-element (nth (third last-response) colors)))))
	 (return-from dino-local-search *guess*))
	((and (= (third last-response) (- (list-length colors) 1)) (not *found-colors*)) ;if all but one of the colors have been guessed, calculate values for last color and generate the first valid guess with the discovered color distribution
	 (setf (nth (- (third last-response) 1) *quantities*) (first last-response))
	 (setf (nth (third last-response) *quantities*) (- board (apply '+ *quantities*))) ;subtract sum so far from total number of pegs to get number of pegs for last color
	 (setf *found-colors* T)
	 (setf *guess* (generate-with-distribution colors *quantities* NIL))
	 (setf *candidates* (append *candidates* (list *guess*)))
	 (setf *already-guessed* (append *already-guessed* (list *guess*)))
	 (if (= (length *candidates*) *beam-width*) (setf *prepared* T))
	 (return-from dino-local-search *guess*))
	((and (< (length *candidates*) *beam-width*) (not *prepared*)) ;initial candidates list not yet filled, add one candidate to it
         (setf (nth (- (length *candidates*) 1) *candidates*) (append (list (nth (- (length *candidates*) 1) *candidates*)) (list (first last-response)))) ;append utility value (pegs in correct position) to last candidate
	 (setf *guess* (generate-with-distribution colors *quantities* *guess*))
	 (setf *candidates* (append *candidates* (list *guess*)))
	 (if (= (length *candidates*) *beam-width*) (setf *prepared* T))
	 (setf *already-guessed* (append *already-guessed* (list *guess*)))
	 (return-from dino-local-search *guess*))
	((< (length *candidates*) (* 2 *beam-width*)) ;generate a new candidate from each of *beam-width* candidates
	 (setf (nth (- (length *candidates*) 1) *candidates*) (append (list (nth (- (length *candidates*) 1) *candidates*)) (list (first last-response)))) ;append utility value (pegs in correct position) to last candidate
	 (if *last-i* (add-knowledge (nth *guess-index* *candidates*) (nth (- (length *candidates*) 1) *candidates*)))
	 (setf *guess-index* (+ 1 *guess-index*))
	 (setf *guess* (generate-successor (first (nth *guess-index* *candidates*))))
	 (setf *candidates* (append *candidates* (list *guess*)))
	 (setf *already-guessed* (append *already-guessed* (list *guess*)))
	 (return-from dino-local-search *guess*))
	((= (length *candidates*) (* 2 *beam-width*)) ;candidates is full - select the best ones and make them the new candidates
	 (setf (nth (- (length *candidates*) 1) *candidates*) (append (list (nth (- (length *candidates*) 1) *candidates*)) (list (first last-response)))) ;append utility value (pegs in correct position) to last candidate
	 (add-knowledge (nth *guess-index* *candidates*) (nth (- (length *candidates*) 1) *candidates*))
	 (loop for n in *candidates* ; currently this loop eliminates any candidate with utility lower than current maximium
	    maximizing (second n) into max
	    counting n into count
	    if (< (second n) max)
	      do (setf (nth (- count 1) *candidates*) NIL)
	    finally (setf *candidates* (remove NIL *candidates*)))
	 (if (> (length *candidates*) *beam-width*) (setf (first *candidates*) NIL)) ;if no candidates were removed, remove the first one.
	 (setf *candidates* (remove NIL *candidates*))
	 (setf *guess-index* 0)  ; reset guess index
	 (setf *guess* (generate-successor (first (nth *guess-index* *candidates*)))) ;generate new successor
	 (setf *candidates* (append *candidates* (list *guess*)))
	 (setf *already-guessed* (append *already-guessed* (list *guess*)))
	 (return-from dino-local-search *guess*))))

;randomly generate i and j
;if positions i and j contain the same number, recursively call this function
;else swap i and j, if resulting swap has already been guessed, call this function
;else if resulting swap is not consistent with known-pegs/wrong-pegs, call this function with proability 1/epsilion
;else return guess with swapped i and j
(defun generate-successor (old-guess)
  (let ((new-guess (copy-list old-guess))
	(i (random (length old-guess)))
	(j (random (length old-guess))))
    (rotatef (nth i new-guess) (nth j new-guess))
    (cond ((eql (nth i old-guess) (nth j old-guess))
	   (return-from generate-successor (generate-successor old-guess)))
	  ((find new-guess *already-guessed* :test #'equal)
	   (return-from generate-successor (generate-successor old-guess)))
	  ((not (consistent-guess new-guess))
	   (cond ((= (random *epsilon*) 1)
		  (setf *already-guessed* (append (list new-guess) *already-guessed*))
		  (setf *last-i* i)
		  (setf *last-j* j)
		  (return-from generate-successor new-guess))
		 (T (return-from generate-successor (generate-successor old-guess)))))
	  (T (setf *already-guessed* (append (list new-guess) *already-guessed*))
	     (setf *last-i* i)
	     (setf *last-j* j)
	     (return-from generate-successor new-guess)))))

(defun consistent-guess (my-guess)
  (loop for i from 0 to (- (list-length *known-pegs*) 1)
     if (and (nth i *known-pegs*) (not (eql (nth i *known-pegs*) (nth i my-guess)))) ;if there is a known peg in position i and the guess doesn't match it
       do (return-from consistent-guess NIL)
     if (and (nth i *wrong-pegs*) (member (nth i my-guess) (nth i *wrong-pegs*))) ;if there are known wrong pegs in position i and the guess matches one
       do (return-from consistent-guess NIL)
     finally (return-from consistent-guess T)))

(defun add-knowledge (old-guess new-guess)
  (cond ((= (second new-guess) (+ (second old-guess) 2 )) ;if correctly positioned pegs increased by 2 after a swap, both new positions are correct
	 (setf (nth *last-i* *known-pegs*) (nth *last-i* (first new-guess)))
	 (setf (nth *last-j* *known-pegs*) (nth *last-j* (first new-guess))))
	((= (second new-guess) (- (second old-guess) 2 )) ;if correctly positioned pegs decreased by 2 after a swap, both old positions are correct
         (setf (nth *last-i* *known-pegs*) (nth *last-i* (first old-guess)))
	 (setf (nth *last-j* *known-pegs*) (nth *last-j* (first old-guess))))
	((= (second new-guess) (+ (second old-guess) 1 )) ;if correctly positioned pegs increased by 1 after a swap, both old positions are wrong
	 (if (not (member (nth *last-i* (first old-guess)) (nth *last-i* *wrong-pegs*)))
	     (setf (nth *last-i* *wrong-pegs*) (append (nth *last-i* *wrong-pegs*) (list (nth *last-i* (first old-guess))))))
	 (if (not (member (nth *last-j* (first old-guess)) (nth *last-j* *wrong-pegs*)))
	     (setf (nth *last-j* *wrong-pegs*) (append (nth *last-j* *wrong-pegs*) (list (nth *last-j* (first old-guess)))))))
	((= (second new-guess) (- (second old-guess) 1 )) ;if correctly positioned pegs decreased by 1 after a swap, both new positions are wrong
	 (if (not (member (nth *last-i* (first new-guess)) (nth *last-i* *wrong-pegs*)))
	     (setf (nth *last-i* *wrong-pegs*) (append (nth *last-i* *wrong-pegs*) (list (nth *last-i* (first new-guess))))))
	 (if (not (member (nth *last-j* (first new-guess)) (nth *last-j* *wrong-pegs*)))
	     (setf (nth *last-j* *wrong-pegs*) (append (nth *last-j* *wrong-pegs*) (list (nth *last-j* (first new-guess)))))))))

