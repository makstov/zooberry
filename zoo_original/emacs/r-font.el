;; Kwangkeun Yi, June 2001
;; adapted from OCaml 2.04 emacs/caml-font.el

;; useful colors

(cond
 ((and (x-display-color-p)
       (not (memq 'font-lock-type-face (face-list))))
  ; make the necessary faces
  (make-face 'Firebrick)
  (set-face-foreground 'Firebrick "Firebrick")
  (make-face 'RosyBrown)
  (set-face-foreground 'RosyBrown "RosyBrown")
  (make-face 'MidnightBlue)
  (set-face-foreground 'MidnightBlue "MidnightBlue")
  (make-face 'DarkGoldenRod)
  (set-face-foreground 'DarkGoldenRod "DarkGoldenRod")
  ; assign them as standard faces
  (setq font-lock-comment-face 'Firebrick)
  (setq font-lock-string-face 'RosyBrown)
  (setq font-lock-function-name-face 'MidnightBlue)
  (setq font-lock-variable-name-face 'DarkGoldenRod)))

; The same definition is in r.el:
; we don't know in which order they will be loaded.
(defvar r-quote-char "'"
  "*Quote for character constants. \"'\" for Rabbit, \"`\" for Rabbit.")

(defconst r-font-lock-keywords
  (list
;comments
;   '("\\(^\\|[^\"]\\)\\((\\*[^*]*\\*+\\([^)*][^*]*\\*+\\)*)\\)"
;     2 font-lock-comment-face)
   '("//[^\n]*" . font-lock-comment-face) 
;character literals
   (cons (concat r-quote-char "\\(\\\\\\([ntbr" r-quote-char "\\]\\|"
		 "[0-9][0-9][0-9]\\)\\|.\\)" r-quote-char
		 "\\|\"[^\"\\]*\\(\\\\\\(.\\|\n\\)[^\"\\]*\\)*\"")
	 'font-lock-string-face)
;labels (and open)
   '("\\([?]?\\<[A-Za-z][A-Za-z0-9_']*:\\)\\([^:=]\\|\\'\\|$\\)" 1
     font-lock-variable-name-face)
   '("[?]?\\<:[A-Za-z][A-Za-z0-9_']*\\>"
     . font-lock-variable-name-face)
;modules and constructors
   '("\\(\\<\\|:\\)\\([A-Z][A-Za-z0-9_']*\\)\\>"
     2 font-lock-function-name-face)
   '("`[A-Za-z][A-Za-z0-9_']*\\>" . font-lock-function-name-face)
;definition
   (cons (concat
	  "\\<\\(a\\(nd\\|s\\)\\|case"
	  "\\|analysis"
	  "\\|signature"
	  "\\|constraint"
	  "\\|set"
	  "\\|lattice"
	  "\\|query"
	  "\\|val\\|eqn\\|mp\\|map\\|f\\(n\\|un\\)\\|let\\)\\>")
	 'font-lock-type-face)
;blocking
   '("\\(\\<\\|:\\)\\(in\\|end\\|sig\\|ana\\)\\|with\\)\\>"
     2 font-lock-variable-name-face)
   
;control
   (cons (concat
	  "\\|\|\\|=>")
	 'font-lock-type-face)
   '("\\<\\>" . font-lock-comment-face)))

(defconst inferior-r-font-lock-keywords
  (append
   (list
;inferior
    '("^[#-]" . font-lock-comment-face)
;labels
    '("[? \t]:[A-Za-z][A-Za-z0-9_']*\\>" . font-lock-variable-name-face))
   r-font-lock-keywords))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defvar r-font-cache '((0 . normal))
  "List of (POSITION . STATE) pairs for an N buffer.
The STATE is either `normal', `comment', or `string'.  The POSITION is
immediately after the token that caused the state change.")

(make-variable-buffer-local 'r-font-cache)

(defun r-font-comments-and-strings (limit)
  "Fontify N comments and strings up to LIMIT.
Handles nested comments and N's escapes for breaking a string over lines.
Uses r-font-cache to maintain the fontification state over the buffer."
  (let ((beg (point))
	last class)
    (while (< beg limit)
      (while (and r-font-cache
		  (> (car (car r-font-cache)) beg))
	(setq r-font-cache (cdr r-font-cache)))
      (setq last (car (car r-font-cache)))
      (setq class (cdr (car r-font-cache)))
      (goto-char last)
      (cond
       ((eq class 'normal)
	(cond
	 ((not (re-search-forward "\\((\\*\\)\\|\\(\"\\)" limit t))
	  (goto-char limit))
	 ((match-beginning 1)
	  (setq r-font-cache (cons (cons (point) 'comment) r-font-cache)))
	 ((match-beginning 2)
	  (setq r-font-cache (cons (cons (point) 'string) r-font-cache)))))
       ((eq class 'comment)
	(cond
	 ((let ((nest 1))
	    (while (and (> nest 0)
			(re-search-forward "\\((\\*\\)\\|\\(\\*)\\)" limit t))
	      (cond
	       ((match-beginning 1) (setq nest (+ nest 1)))
	       ((match-beginning 2) (setq nest (- nest 1)))))
	    (> nest 0))
	  (goto-char limit))
	 (t
	  (setq r-font-cache (cons (cons (point) 'normal) r-font-cache))))
	(put-text-property (- last 2) (point) 'face 'font-lock-comment-face))
       ((eq class 'string)
	(while (and (re-search-forward
		     "\\(\"\\)\\|\\(\\\\\\s-*\\\\\\)\\|\\(\\\\\"\\)" limit t)
		     (not (match-beginning 1))))
	(cond
	 ((match-beginning 1)
	  (setq r-font-cache (cons (cons (point) 'normal) r-font-cache)))
	 (t
	  (goto-char limit)))
	(put-text-property (- last 1) (point) 'face 'font-lock-string-face)))
      (setq beg (point)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; font-lock commands are similar for r-mode and inferior-r-mode
(defvar r-font-lock-all nil
  "Font-lock matchers for N.")

(setq r-mode-hook
      '(lambda ()
         (let ((new-font-lock (fboundp 'global-font-lock-mode)))
           (or r-font-lock-all
               (setq r-font-lock-all
                     (append
                      (and new-font-lock
                           (list (list 'r-font-comments-and-strings)))
                      r-font-lock-keywords)))
           (cond
            (new-font-lock
             (make-local-variable 'font-lock-defaults)
             (setq font-lock-defaults '(r-font-lock-all t)))
            (t
             (setq font-lock-keywords r-font-lock-all))))
	 (make-local-variable 'font-lock-keywords-only)
	 (setq font-lock-keywords-only t)
	 (font-lock-mode 1)))

(defvar inferior-r-font-lock-all nil
  "Font-lock matchers for inferior N.")

(setq inferior-r-mode-hook
      '(lambda ()
         (let ((new-font-lock (fboundp 'global-font-lock-mode)))
           (or inferior-r-font-lock-all
               (setq inferior-r-font-lock-all
                     (append
                      (and new-font-lock
                           (list (list 'r-font-comments-and-strings)))
                      inferior-r-font-lock-keywords)))
           (cond
            (new-font-lock
             (make-local-variable 'font-lock-defaults)
             (setq font-lock-defaults '(inferior-r-font-lock-all t)))
            (t
             (setq font-lock-keywords inferior-r-font-lock-all))))
	 (make-local-variable 'font-lock-keywords-only)
	 (setq font-lock-keywords-only t)
	 (font-lock-mode 1)))

(provide 'r-font)


