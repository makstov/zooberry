;;; n.el --- N code editing commands for Emacs
;;; adapted from OCaml 2.04 emacs/caml.el

;; Kwangkeun Yi, Feb 2000

;;indentation code is Copyright (C) 1996 by Ian T Zimmerman <itz@rahul.net>
;;copying: covered by the current FSF General Public License.

;; indentation code adapted for Objective Caml by Jacques Garrigue,
;; july 1997. <garrigue@kurims.kyoto-u.ac.jp>

;;user customizable variables
(defvar r-quote-char "'"
  "*Quote for character constants. \"'\" for R, \"`\" for R.")

(defvar r-imenu-enable nil
  "*Enable Imenu support.")

(defvar r-olabl-disable nil
  "*Disable O'Labl support")

(defvar r-mode-indentation 2
  "*Used for \\[r-unindent-command].")

(defvar r-lookback-limit 5000
  "*How far to look back for syntax things in n mode.")

(defvar r-max-indent-priority 8
  "*Bounds priority of operators permitted to affect n indentation.

Priorities are assigned to `interesting' n operators as follows:

	all keywords 0 to 7	8
	type, val, ... + 0	7
	:: ^			6
	@			5
	:= <-			4
	if			3
	fun, let, match ...	2
	module			1
	opening keywords 	0.")

(defvar r-apply-extra-indent 2
  "*How many spaces to add to indentation for an application in n mode.")
(make-variable-buffer-local 'r-apply-extra-indent)

(defvar r-begin-indent 2
  "*How many spaces to indent from a begin keyword in n mode.")
(make-variable-buffer-local 'r-begin-indent)

(defvar r-class-indent 2
  "*How many spaces to indent from a class keyword in n mode.")
(make-variable-buffer-local 'r-class-indent)

(defvar r-exception-indent 2
  "*How many spaces to indent from a exception keyword in n mode.")
(make-variable-buffer-local 'r-exception-indent)

(defvar r-for-indent	2
  "*How many spaces to indent from a for keyword in n mode.")
(make-variable-buffer-local 'r-for-indent)

(defvar r-fun-indent	2
  "*How many spaces to indent from a fun keyword in n mode.")
(make-variable-buffer-local 'r-fun-indent)

(defvar r-function-indent 4
  "*How many spaces to indent from a function keyword in n mode.")
(make-variable-buffer-local 'r-function-indent)

(defvar r-if-indent	2
  "*How many spaces to indent from a if keyword in n mode.")
(make-variable-buffer-local 'r-if-indent)

(defvar r-if-else-indent 0
  "*How many spaces to indent from an if .. else line in n mode.")
(make-variable-buffer-local 'r-if-else-indent)

(defvar r-inherit-indent 2
  "*How many spaces to indent from a inherit keyword in n mode.")
(make-variable-buffer-local 'r-inherit-indent)

(defvar r-initializer-indent 2
  "*How many spaces to indent from a initializer keyword in n mode.")
(make-variable-buffer-local 'r-initializer-indent)

(defvar r-include-indent 2
  "*How many spaces to indent from a include keyword in n mode.")
(make-variable-buffer-local 'r-include-indent)

(defvar r-let-indent	2
  "*How many spaces to indent from a let keyword in n mode.")
(make-variable-buffer-local 'r-let-indent)

(defvar r-let-in-indent 0
  "*How many spaces to indent from a let .. in keyword in n mode.")
(make-variable-buffer-local 'r-let-in-indent)

(defvar r-match-indent 2
  "*How many spaces to indent from a match keyword in n mode.")
(make-variable-buffer-local 'r-match-indent)

(defvar r-method-indent 2
  "*How many spaces to indent from a method keyword in n mode.")
(make-variable-buffer-local 'r-method-indent)

(defvar r-module-indent 2
  "*How many spaces to indent from a module keyword in n mode.")
(make-variable-buffer-local 'r-module-indent)

(defvar r-object-indent 2
  "*How many spaces to indent from a object keyword in n mode.")
(make-variable-buffer-local 'r-object-indent)

(defvar r-of-indent 2
  "*How many spaces to indent from a of keyword in n mode.")
(make-variable-buffer-local 'r-of-indent)

(defvar r-parser-indent 4
  "*How many spaces to indent from a parser keyword in n mode.")
(make-variable-buffer-local 'r-parser-indent)

(defvar r-sig-indent 2
  "*How many spaces to indent from a sig keyword in n mode.")
(make-variable-buffer-local 'r-sig-indent)

(defvar r-struct-indent 2
  "*How many spaces to indent from a struct keyword in n mode.")
(make-variable-buffer-local 'r-struct-indent)

(defvar r-try-indent	2
  "*How many spaces to indent from a try keyword in n mode.")
(make-variable-buffer-local 'r-try-indent)

(defvar r-type-indent 4
  "*How many spaces to indent from a type keyword in n mode.")
(make-variable-buffer-local 'r-type-indent)

(defvar r-val-indent	2
  "*How many spaces to indent from a val keyword in n mode.")
(make-variable-buffer-local 'r-val-indent)

(defvar r-while-indent 2
  "*How many spaces to indent from a while keyword in n mode.")
(make-variable-buffer-local 'r-while-indent)

(defvar r-::-indent	2
  "*How many spaces to indent from a :: operator in n mode.")
(make-variable-buffer-local 'r-::-indent)

(defvar r-@-indent	2
  "*How many spaces to indent from a @ operator in n mode.")
(make-variable-buffer-local 'r-@-indent)

(defvar r-:=-indent  2
  "*How many spaces to indent from a := operator in n mode.")
(make-variable-buffer-local 'r-:=-indent)

(defvar r-<--indent	2
  "*How many spaces to indent from a <- operator in n mode.")
(make-variable-buffer-local 'r-<--indent)

(defvar r-->-indent	2
  "*How many spaces to indent from a -> operator in n mode.")
(make-variable-buffer-local 'r-->-indent)

(defvar r-lb-indent 2
  "*How many spaces to indent from a \[ operator in n mode.")
(make-variable-buffer-local 'r-lb-indent)

(defvar r-lc-indent 2
  "*How many spaces to indent from a \{ operator in n mode.")
(make-variable-buffer-local 'r-lc-indent)

(defvar r-lp-indent	1
  "*How many spaces to indent from a \( operator in n mode.")
(make-variable-buffer-local 'r-lp-indent)

(defvar r-and-extra-indent nil
  "*Extra indent for n lines starting with the and keyword.
Usually negative. nil is align on master.")
(make-variable-buffer-local 'r-and-extra-indent)

(defvar r-do-extra-indent nil
  "*Extra indent for n lines starting with the do keyword.
Usually negative. nil is align on master.")
(make-variable-buffer-local 'r-do-extra-indent)

(defvar r-done-extra-indent nil
  "*Extra indent for n lines starting with the done keyword.
Usually negative. nil is align on master.")
(make-variable-buffer-local 'r-done-extra-indent)

(defvar r-else-extra-indent nil
  "*Extra indent for n lines starting with the else keyword.
Usually negative. nil is align on master.")
(make-variable-buffer-local 'r-else-extra-indent)

(defvar r-end-extra-indent nil
  "*Extra indent for n lines starting with the end keyword.
Usually negative. nil is align on master.")
(make-variable-buffer-local 'r-end-extra-indent)

(defvar r-in-extra-indent nil
  "*Extra indent for n lines starting with the in keyword.
Usually negative. nil is align on master.")
(make-variable-buffer-local 'r-in-extra-indent)

(defvar r-then-extra-indent nil
  "*Extra indent for n lines starting with the then keyword.
Usually negative. nil is align on master.")
(make-variable-buffer-local 'r-then-extra-indent)

(defvar r-to-extra-indent -1
  "*Extra indent for n lines starting with the to keyword.
Usually negative. nil is align on master.")
(make-variable-buffer-local 'r-to-extra-indent)

(defvar r-with-extra-indent nil
  "*Extra indent for n lines starting with the with keyword.
Usually negative. nil is align on master.")
(make-variable-buffer-local 'r-with-extra-indent)

(defvar r-comment-indent 3
  "*Indent inside comments.")
(make-variable-buffer-local 'r-comment-indent)

(defvar r-|-extra-indent -2
  "*Extra indent for n lines starting with the | operator.
Usually negative. nil is align on master.")
(make-variable-buffer-local 'r-|-extra-indent)

(defvar r-rb-extra-indent -2
  "*Extra indent for n lines statring with ].
Usually negative. nil is align on master.")

(defvar r-rc-extra-indent -2
  "*Extra indent for n lines starting with }.
Usually negative. nil is align on master.")

(defvar r-rp-extra-indent -1
  "*Extra indent for n lines starting with ).
Usually negative. nil is align on master.")

(defvar r-electric-indent t
  "*Non-nil means electrically indent lines starting with |, ] or }.

Many people find eletric keys irritating, so you can disable them if
you are one.")

(defvar r-electric-close-vector t
  "*Non-nil means electrically insert a | before a vector-closing ].

Many people find eletric keys irritating, so you can disable them if
you are one. You should probably have this on, though, if you also
have r-electric-indent on, which see.")

;;code
(if (or (not (fboundp 'indent-line-to))
	(not (fboundp 'buffer-substring-no-properties)))
    (require 'r-compat))

(defvar r-shell-active nil
  "*Non nil when a subshell is running.")

;; is it really ok ? Conform to Xemacs definition
(if (not (boundp 'running-xemacs)) (setq running-xemacs nil))

(defvar r-mode-map nil
  "Keymap used in Rabbit mode.")
(if r-mode-map
    ()
  (setq r-mode-map (make-sparse-keymap))
  (define-key r-mode-map "|" 'r-electric-pipe)
  (define-key r-mode-map "}" 'r-electric-pipe)
  (define-key r-mode-map "]" 'r-electric-rb)
  (define-key r-mode-map "\t" 'r-indent-command)
  (define-key r-mode-map [backtab] 'r-unindent-command)

;itz 04-21-96 instead of defining a new function, use defadvice
;that way we get out effect even when we do \C-x` in compilation buffer  
;  (define-key r-mode-map "\C-x`" 'r-next-error)

  (define-key r-mode-map "\177" 'backward-delete-char-untabify)
  (define-key r-mode-map "\C-cb" 'r-insert-begin-form)
  (define-key r-mode-map "\C-cf" 'r-insert-for-form)
  (define-key r-mode-map "\C-ci" 'r-insert-if-form)
  (define-key r-mode-map "\C-cl" 'r-insert-let-form)
  (define-key r-mode-map "\C-cm" 'r-insert-match-form)
  (define-key r-mode-map "\C-ct" 'r-insert-try-form)
  (define-key r-mode-map "\C-cw" 'r-insert-while-form)
  (define-key r-mode-map "\C-c`" 'r-goto-phrase-error)
  (define-key r-mode-map "\C-c\C-a" 'r-find-alternate-file)
  (define-key r-mode-map "\C-c\C-c" 'compile)
  (define-key r-mode-map "\C-c\C-e" 'r-eval-phrase)
  (define-key r-mode-map "\C-c\C-\[" 'r-backward-to-less-indent)
  (define-key r-mode-map "\C-c\C-\]" 'r-forward-to-less-indent)
  (define-key r-mode-map "\C-c\C-q" 'r-indent-phrase)
  (define-key r-mode-map "\C-c\C-r" 'r-eval-region)
  (define-key r-mode-map "\C-c\C-s" 'r-show-subshell)
  (define-key r-mode-map "\M-\C-h" 'r-mark-phrase)
  (define-key r-mode-map "\M-\C-q" 'r-indent-phrase)
  (define-key r-mode-map "\M-\C-x" 'r-eval-phrase)
  (if running-xemacs nil ; if not running xemacs
    (let ((map (make-sparse-keymap "Caml"))
	  (forms (make-sparse-keymap "Forms")))
      (define-key r-mode-map "\C-c\C-d" 'r-show-imenu)
      (define-key r-mode-map [menu-bar] (make-sparse-keymap))
      (define-key r-mode-map [menu-bar n] (cons "Caml" map))
      (define-key map [run-n] '("Start subshell..." . run-n))
      (define-key map [compile] '("Compile..." . compile))
      (define-key map [switch-view]
	'("Switch view" . r-find-alternate-file))
      (define-key map [separator-format] '("--"))
      (define-key map [forms] (cons "Forms" forms))
      (define-key map [show-imenu] '("Show index" . r-show-imenu))
      (put 'r-show-imenu 'menu-enable '(not r-imenu-shown))
      (define-key map [show-subshell] '("Show subshell" . r-show-subshell))
      (put 'r-show-subshell 'menu-enable 'r-shell-active)
      (define-key map [eval-phrase] '("Eval phrase" . r-eval-phrase))
      (put 'r-eval-phrase 'menu-enable 'r-shell-active)
      (define-key map [indent-phrase] '("Indent phrase" . r-indent-phrase))
      (define-key forms [while]
	'("while .. do .. done" . r-insert-while-form))
      (define-key forms [try] '("try .. with .." . r-insert-try-form))
      (define-key forms [match] '("match .. with .." . r-insert-match-form))
      (define-key forms [let] '("let .. in .." . r-insert-let-form))
      (define-key forms [if] '("if .. then .. else .." . r-insert-if-form))
      (define-key forms [begin] '("for .. do .. done" . r-insert-for-form))
      (define-key forms [begin] '("begin .. end" . r-insert-begin-form)))))

(defvar r-mode-xemacs-menu
  (if running-xemacs
      '("Caml"
	[ "Indent phrase" r-indent-phrase :keys "C-M-q" ]
	[ "Eval phrase" r-eval-phrase
	  :active r-shell-active :keys "C-M-x" ]
	[ "Show subshell" r-show-subshell r-shell-active ]
	("Forms"
	 [ "while .. do .. done" r-insert-while-form t]
	 [ "try .. with .." r-insert-try-form t ]
	 [ "match .. with .." r-insert-match-form t ]
	 [ "let .. in .." r-insert-let-form t ]
	 [ "if .. then .. else .." r-insert-if-form t ]
	 [ "for .. do .. done" r-insert-for-form t ]
	 [ "begin .. end" r-insert-begin-form t ])
	"---"
	[ "Switch view" r-find-alternate-file t ]
	[ "Compile..." compile t ]
	[ "Start subshell..." run-n t ]))
  "Menu to add to the menubar when running Xemacs")

(defvar r-mode-syntax-table nil
  "Syntax table in use in Caml mode buffers.")
(if r-mode-syntax-table
    ()
  (setq r-mode-syntax-table (make-syntax-table))
  ; backslash is an escape sequence
  (modify-syntax-entry ?\\ "\\" r-mode-syntax-table)
  ; ( is first character of comment start
  (modify-syntax-entry ?\( "()1" r-mode-syntax-table)
  ; * is second character of comment start,
  ; and first character of comment end
  (modify-syntax-entry ?*  ". 23" r-mode-syntax-table)
  ; ) is last character of comment end
  (modify-syntax-entry ?\) ")(4" r-mode-syntax-table)
  ; backquote was a string-like delimiter (for character literals)
  ; (modify-syntax-entry ?` "\"" r-mode-syntax-table)
  ; quote and underscore are part of words
  (modify-syntax-entry ?' "w" r-mode-syntax-table)
  (modify-syntax-entry ?_ "w" r-mode-syntax-table)
  ; : is part of words (labels) in O'Labl
  (if r-olabl-disable nil 
    (modify-syntax-entry ?: "w" r-mode-syntax-table))
  ; ISO-latin accented letters and EUC kanjis are part of words
  (let ((i 160))
    (while (< i 256)
      (modify-syntax-entry i "w" r-mode-syntax-table)
      (setq i (1+ i)))))

(defvar r-mode-abbrev-table nil
  "Abbrev table used for Caml mode buffers.")
(if r-mode-abbrev-table nil
  (setq r-mode-abbrev-table (make-abbrev-table))
  (define-abbrev r-mode-abbrev-table "and" "and" 'r-abbrev-hook)
  (define-abbrev r-mode-abbrev-table "do" "do" 'r-abbrev-hook)
  (define-abbrev r-mode-abbrev-table "done" "done" 'r-abbrev-hook)
  (define-abbrev r-mode-abbrev-table "else" "else" 'r-abbrev-hook)
  (define-abbrev r-mode-abbrev-table "end" "end" 'r-abbrev-hook)
  (define-abbrev r-mode-abbrev-table "in" "in" 'r-abbrev-hook)
  (define-abbrev r-mode-abbrev-table "then" "then" 'r-abbrev-hook)
  (define-abbrev r-mode-abbrev-table "with" "with" 'r-abbrev-hook))

;;; The major mode
(eval-when-compile
  (if (and (boundp 'running-xemacs) running-xemacs) nil
    (require 'imenu)))

(defun r-mode ()
  "Major mode for editing Rabbit code.

\\{r-mode-map}"

  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'r-mode)
  (setq mode-name "r")
  (use-local-map r-mode-map)
  (set-syntax-table r-mode-syntax-table)
  (setq local-abbrev-table r-mode-abbrev-table)
  (make-local-variable 'paragraph-start)
  (setq paragraph-start (concat "^$\\|" page-delimiter))
  (make-local-variable 'paragraph-separate)
  (setq paragraph-separate paragraph-start)
  (make-local-variable 'paragraph-ignore-fill-prefix)
  (setq paragraph-ignore-fill-prefix t)
  (make-local-variable 'require-final-newline)
  (setq require-final-newline t)
  (make-local-variable 'comment-start)
  (setq comment-start "(*")
  (make-local-variable 'comment-end)
  (setq comment-end "*)")
  (make-local-variable 'comment-column)
  (setq comment-column 40)
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "(\\*+ *")
  (make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments nil)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'r-indent-command)
  ;itz Fri Sep 25 13:23:49 PDT 1998
  (make-local-variable 'add-log-current-defun-function)
  (setq add-log-current-defun-function 'r-current-defun)
  ;itz 03-25-96
  (setq before-change-function 'r-before-change-function)
  (setq r-last-noncomment-pos nil)
  (setq r-last-comment-start (make-marker))
  (setq r-last-comment-end (make-marker))
  ;garrigue 27-11-96
  (setq case-fold-search nil)
  ;garrigue july 97
  (if running-xemacs ; from Xemacs lisp mode
      (if (and (featurep 'menubar)
	       current-menubar)
	  (progn
	    ;; make a local copy of the menubar, so our modes don't
	    ;; change the global menubar
	    (set-buffer-menubar current-menubar)
	    (add-submenu nil r-mode-xemacs-menu)))
    ;imenu support (not for Xemacs)
    (make-local-variable 'imenu-create-index-function)
    (setq imenu-create-index-function 'r-create-index-function)
    (make-local-variable 'imenu-generic-expression)
    (setq imenu-generic-expression r-imenu-search-regexp)
    (make-local-variable 'r-imenu-shown)
    (setq r-imenu-shown nil)
    (if (and r-imenu-enable (< (buffer-size) 10000))
	(r-show-imenu)))
  ;; Kwang 2/8/00
  ;(require 'r-font)
  ;; Kwang end
  (run-hooks 'r-mode-hook))

;;; Auxiliary function. Garrigue 96-11-01.

(defun r-find-alternate-file ()
  (interactive)
  (let ((name (buffer-file-name)))
    (if (string-match "^\\(.*\\)\\.\\(r\\|ri\\)$" name)
	(find-file
	 (concat
	  (r-match-string 1 name)
	  (if (string= "r" (r-match-string 2 name)) ".r" ".ri"))))))

;;; subshell support

(defun r-eval-region (start end))
;  "Send the current region to the inferior Caml process."
;  (interactive "r")
;  (inferior-n-eval-region start end))

(defun r-eval-phrase ()0
;  "Send the current Caml phrase to the inferior Caml process."
;  (interactive)
;  (save-excursion
;    (let ((bounds (r-mark-phrase)))
;    (inferior-n-eval-region (car bounds) (cdr bounds)))))
;
(defun r-show-subshell ())
;  (interactive)
;  (inferior-n-show-subshell))

;;; Imenu support
(defun r-show-imenu ())
;  (interactive)
;  (require 'imenu)
;  (switch-to-buffer (current-buffer))
;  (imenu-add-to-menubar "Defs")
;  (setq r-imenu-shown t))

(defconst r-imenu-search-regexp "")
;  (concat "\\<in\\>\\|"
;	  "^[ \t]*\\(let\\|class\\|type\\|m\\(odule\\|ethod\\)"
;	  "\\|functor\\|and\\|val\\)[ \t]+"
;	  "\\(\\('[a-zA-Z0-9]+\\|([^)]+)"
;	  "\\|mutable\\|private\\|rec\\|type\\)[ \t]+\\)?"
;	  "\\([a-zA-Z][a-zA-Z0-9_']*\\)"))

(defun r-prev-index-position-function ()
  (let (found data)
    (while (and (setq found
		      (re-search-backward r-imenu-search-regexp nil 'move))
		(progn (setq data (match-data)) t)
		(or (r-in-literal-p)
		    (r-in-comment-p)
		    (if (looking-at "in") (r-find-in-match)))))
    (set-match-data data)
    found))
(defun r-create-index-function ()
  (let (value-alist
	type-alist
	class-alist
	method-alist
	module-alist
	and-alist
	all-alist
	menu-alist
	(prev-pos (point-max))
	index)
    (goto-char prev-pos)
    (imenu-progress-message prev-pos 0 t)
    ;; collect definitions
    (while (r-prev-index-position-function)
      (setq index (cons (r-match-string 5) (point)))
      (imenu-progress-message prev-pos nil t)
      (setq all-alist (cons index all-alist))
      (cond
       ((looking-at "[ \t]*and")
	(setq and-alist (cons index and-alist)))
       ((looking-at "[ \t]*let")
	(setq value-alist (cons index (append and-alist value-alist)))
	(setq and-alist nil))
       ((looking-at "[ \t]*type")
	(setq type-alist (cons index (append and-alist type-alist)))
	(setq and-alist nil))
       ((looking-at "[ \t]*class")
	(setq class-alist (cons index (append and-alist class-alist)))
	(setq and-alist nil))
       ((looking-at "[ \t]*val")
	(setq value-alist (cons index value-alist)))
       ((looking-at "[ \t]*\\(module\\|functor\\)")
	(setq module-alist (cons index module-alist)))
       ((looking-at "[ \t]*method")
	(setq method-alist (cons index method-alist)))))
    ;; build menu
    (mapcar
     '(lambda (pair)
	(if (symbol-value (cdr pair))
	    (setq menu-alist
		  (cons
		   (cons (car pair)
			 (sort (symbol-value (cdr pair)) 'imenu--sort-by-name))
		   menu-alist))))
     '(("Values" . value-alist)
       ("Types" . type-alist)
       ("Modules" . module-alist)
       ("Methods" . method-alist)
       ("Classes" . class-alist)))
    (if all-alist (setq menu-alist (cons (cons "Index" all-alist) menu-alist)))
    (imenu-progress-message prev-pos 100 t)
    menu-alist))

;;; Indentation stuff

(defun r-in-indentation ()
  "Tests whether all characters between beginning of line and point
are blanks."
  (save-excursion
    (skip-chars-backward " \t")
    (bolp)))

;;; The command
;;; Sorry, I didn't like the previous behaviour... Garrigue 96/11/01

(defun r-indent-command (&optional p)
  "Indent the current line in Caml mode.

Compute new indentation based on n syntax. If prefixed, indent
the line all the way to where point is."

  (interactive "*p")
  (cond
   ((and p (> p 1)) (indent-line-to (current-column)))
   ((r-in-indentation) (indent-line-to (r-compute-final-indent)))
   (t (save-excursion
	(indent-line-to
	 (r-compute-final-indent))))))
   
(defun r-unindent-command ()

  "Decrease indentation by one level in Caml mode.  

Works only if the point is at the beginning of an indented line
\(i.e. all characters between beginning of line and point are
blanks\).  Does nothing otherwise. The unindent size is given by the
variable r-mode-indentation."

  (interactive "*")
  (let* ((begline
          (save-excursion
            (beginning-of-line)
            (point)))
         (current-offset
          (- (point) begline)))
    (if (and (>= current-offset r-mode-indentation)
             (r-in-indentation))
        (backward-delete-char-untabify r-mode-indentation))))

;;;
;;; Error processing
;;;

;; Error positions are given in bytes, not in characters
;; This function switches to monobyte mode

(if (not (fboundp 'char-bytes))
    (defalias 'forward-byte 'forward-char)
  (defun r-char-bytes (ch)
    (let ((l (char-bytes ch)))
      (if (> l 1) (- l 1) l)))
  (defun forward-byte (count)
    (if (> count 0)
	(while (> count 0)
	  (setq count (- count (r-char-bytes (char-after))))
	  (forward-char))
      (while (< count 0)
	(setq count (+ count (r-char-bytes (char-before))))
	(backward-char)))))

(require 'compile)

;; In Emacs 19, the regexps in compilation-error-regexp-alist do not
;; match the error messages when the language is not English.
;; Hence we add a regexp.

(defconst r-error-regexp
  "^[A-\377]+ \"\\([^\"\n]+\\)\", [A-\377]+ \\([0-9]+\\)[-,:]"
  "Regular expression matching the error messages produced by nc.")

(if (boundp 'compilation-error-regexp-alist)
    (or (assoc r-error-regexp
               compilation-error-regexp-alist)
        (setq compilation-error-regexp-alist
              (cons (list r-error-regexp 1 2)
               compilation-error-regexp-alist))))

;; A regexp to extract the range info

(defconst r-error-chars-regexp
  ".*, .*, [A-\377]+ \\([0-9]+\\)-\\([0-9]+\\):"
  "Regular expression extracting the character numbers
from an error message produced by nc.")

;; Wrapper around next-error.

(defvar r-error-overlay nil)

;;itz 04-21-96 somebody didn't get the documetation for next-error
;;right. When the optional argument is a number n, it should move
;;forward n errors, not reparse.

;itz 04-21-96 instead of defining a new function, use defadvice
;that way we get our effect even when we do \C-x` in compilation buffer  

(defadvice next-error (after r-next-error activate)
 "Reads the extra positional information provided by the Caml compiler.

Puts the point and the mark exactly around the erroneous program
fragment. The erroneous fragment is also temporarily highlighted if
possible."

 (if (eq major-mode 'r-mode)
     (let (bol beg end)
       (save-excursion
	 (set-buffer
	  (if (boundp 'compilation-last-buffer) 
	      compilation-last-buffer	;Emacs 19
	    "*compilation*"))		;Emacs 18
	 (save-excursion
	   (goto-char (window-point (get-buffer-window (current-buffer))))
	   (if (looking-at r-error-chars-regexp)
	       (setq beg
		     (string-to-int
		      (buffer-substring (match-beginning 1) (match-end 1)))
		     end
		     (string-to-int
		      (buffer-substring (match-beginning 2) (match-end 2)))))))
       (cond (beg
	      (setq end (- end beg))
              (beginning-of-line)
	      (forward-byte beg)
	      (setq beg (point))
	      (forward-byte end)
	      (setq end (point))
	      (goto-char beg)
	      (push-mark end t)
	      (cond ((fboundp 'make-overlay)
		     (if r-error-overlay ()
		       (setq r-error-overlay (make-overlay 1 1))
		       (overlay-put r-error-overlay 'face 'region))
		     (unwind-protect
			 (progn
			   (move-overlay r-error-overlay
					 beg end (current-buffer))
			   (sit-for 60))
		       (delete-overlay r-error-overlay)))))))))

;; Usual match-string doesn't work properly with font-lock-mode
;; on some emacs.

(defun r-match-string (num &optional string)

  "Return string of text matched by last search, without properties.

NUM specifies which parenthesized expression in the last regexp.
Value is nil if NUMth pair didn't match, or there were less than NUM
pairs.  Zero means the entire text matched by the whole regexp or
whole string."

  (let* ((data (match-data))
	 (begin (nth (* 2 num) data))
	 (end (nth (1+ (* 2 num)) data)))
    (if string (substring string begin end)
      (buffer-substring-no-properties begin end))))

;; itz Thu Sep 24 19:02:42 PDT 1998 this is to have some level of
;; comfort when sending phrases to the toplevel and getting errors.
(defun r-goto-phrase-error ()
  "Find the error location in current Caml phrase."
  (interactive)
  (let ((bounds (save-excursion (r-mark-phrase))))
    (inferior-n-goto-error (car bounds) (cdr bounds))))

;;; Phrases

;itz the heuristics used to see if we're `between two phrases'
;didn't seem right to me.

(defconst r-phrase-start-keywords
  (concat "\\<\\(class\\|ex\\(ternal\\|ception\\)\\|functor"
	  "\\|let\\|module\\|open\\|type\\|val\\)\\>")
  "Keywords starting phrases in files")

;; a phrase starts when a toplevel keyword is at the beginning of a line
(defun r-at-phrase-start-p ()
  (and (bolp)
       (or (looking-at "#")
	   (looking-at r-phrase-start-keywords))))

(defun r-mark-phrase ()
  "Put mark at end of this N phrase, point at beginning.

The N phrase is the phrase just before the point.
Adapted from J. Garrigue version for Objective Caml and Caml-Light."

  (interactive)
  (let (use-semi end)
    (if (and (looking-at ";") (not (r-in-comment-p))) nil
      (if (r-at-phrase-start-p) (forward-char))
      (while (and (cond
		   ((re-search-forward
		     (concat ";\\|" r-phrase-start-keywords) nil 'move)
		    (goto-char (match-beginning 0)) t))
		  (or (not (or (bolp) (looking-at ";")))
		      (r-in-comment-p)
		      (r-in-literal-p)))
	(forward-char)))
    (setq use-semi (looking-at ";"))
    (skip-chars-backward " \n\t")
    (while (and (eq (preceding-char) ?\)) (eq (char-after (- (point) 2)) ?*))
      (backward-char)
      (while (r-in-comment-p) (search-backward comment-start))
      (skip-chars-backward " \n\t"))
    (push-mark)
    (setq end (point))
    (cond
     (use-semi
      (if (r-find-kwop ";") (forward-char 2)
	(goto-char (point-min)))
      (skip-chars-forward " \n\t")
      (while (or (looking-at comment-start-skip) (r-in-comment-p))
	(if (= (following-char) ?\)) (forward-char)
	  (search-forward comment-end))
	(skip-chars-forward " \n\t")))
     (t
      (if (not (r-find-kwop r-phrase-start-keywords))
	  (error "No phrase preceding point"))
      (while (and (or (not (bolp))
		      (r-in-comment-p)
		      (r-in-literal-p))
		  (r-find-kwop r-phrase-start-keywords)))))
    (cons (point) end)))

;;itz Fri Sep 25 12:58:13 PDT 1998 support for adding change-log entries
(defun r-current-defun ()
  (save-excursion
    (r-mark-phrase)
    (if (not (looking-at r-phrase-start-keywords)) nil
      (re-search-forward r-phrase-start-keywords)
      (let ((done nil))
        (while (not done)
          (cond
           ((looking-at "\\s ")
            (skip-syntax-forward " "))
           ((char-equal (following-char) ?\( )
            (forward-sexp 1))
           ((char-equal (following-char) ?')
            (skip-syntax-forward "w_"))
           (t (setq done t)))))
      (re-search-forward "\\(\\sw\\|\\s_\\)+")
      (match-string 0))))

(defvar r-last-noncomment-pos nil
  "Caches last buffer position determined not inside a n comment.")
(make-variable-buffer-local 'r-last-noncomment-pos)

;;last-noncomment-pos can be a simple position, because we nil it
;;anyway whenever buffer changes upstream. last-comment-start and -end
;;have to be markers, because we preserve them when the changes' end
;;doesn't overlap with the comment's start.

(defvar r-last-comment-start nil
  "A marker caching last determined n comment start.")
(make-variable-buffer-local 'r-last-comment-start)

(defvar r-last-comment-end nil
  "A marker caching last determined n comment end.")
(make-variable-buffer-local 'r-last-comment-end)

(make-variable-buffer-local 'before-change-function)

(defun r-overlap (b1 e1 b2 e2)
  (<= (max b1 b2) (min e1 e2)))

;this clears the last comment cache if necessary
(defun r-before-change-function (begin end)
  (if (and r-last-noncomment-pos
	   (> r-last-noncomment-pos begin))
      (setq r-last-noncomment-pos nil))
  (if (and (marker-position r-last-comment-start)
	   (marker-position r-last-comment-end)
	   (r-overlap begin end
			 r-last-comment-start
			 r-last-comment-end))
      (prog2
	  (set-marker r-last-comment-start nil)
	  (set-marker r-last-comment-end nil)))
  (let ((orig-function (default-value 'before-change-function)))
    (if orig-function (funcall orig-function begin end))))

(defun r-in-literal-p ()
  "Returns non-nil if point is inside a n literal."
  (let* ((start-literal (concat "[\"" r-quote-char "]"))
	 (char-literal
	  (concat "\\([^\\]\\|\\\\\\.\\|\\\\[0-9][0-9][0-9]\\)"
		  r-quote-char))
	 (pos (point))
	 (eol (progn (end-of-line 1) (point)))
	 state in-str)
    (beginning-of-line 1)
    (while (and (not state)
		(re-search-forward start-literal eol t)
		(<= (point) pos))
      (cond
       ((string= (r-match-string 0) "\"")
	(setq in-str t)
	(while (and in-str (not state)
		    (re-search-forward "\"\\|\\\\\"" eol t))
	  (if (> (point) pos) (setq state t))
	  (if (string= (r-match-string 0) "\"") (setq in-str nil)))
	(if in-str (setq state t)))
       ((looking-at char-literal)
	(if (and (>= pos (match-beginning 0)) (< pos (match-end 0)))
	    (setq state t)
	  (goto-char (match-end 0))))))
    (goto-char pos)
    state))

(defun r-forward-comment ()
  "Skip one (eventually nested) comment."
  (let ((count 1) match)
    (while (> count 0)
      (if (not (re-search-forward "(\\*\\|\\*)" nil 'move))
	  (setq count -1)
	(setq match (r-match-string 0))
	(cond
	 ((r-in-literal-p)
	  nil)
	 ((string= match comment-start)
	  (setq count (1+ count)))
	 (t
	  (setq count (1- count))))))
    (= count 0)))

(defun r-backward-comment ()
  "Skip one (eventually nested) comment."
  (let ((count 1) match)
    (while (> count 0)
      (if (not (re-search-backward "(\\*\\|\\*)" nil 'move))
	  (setq count -1)
	(setq match (r-match-string 0))
	(cond
	 ((r-in-literal-p)
	  nil)
	 ((string= match comment-start)
	  (setq count (1- count)))
	 (t
	  (setq count (1+ count))))))
    (= count 0)))

(defun r-in-comment-p ()
  "Returns non-nil if point is inside a n comment.
Returns nil for the parenthesis openning a comment."
  ;;we look for comments differently than literals. there are two
  ;;reasons for this. first, n has nested comments and it is not so
  ;;clear that parse-partial-sexp supports them; second, if proper
  ;;style is used, literals are never split across lines, so we don't
  ;;have to worry about bogus phrase breaks inside literals, while we
  ;;have to account for that possibility in comments.
  (save-excursion
    (let* ((cached-pos r-last-noncomment-pos)
	   (cached-begin (marker-position r-last-comment-start))
	   (cached-end (marker-position r-last-comment-end)))
      (cond
       ((and cached-begin cached-end
	     (< cached-begin (point)) (< (point) cached-end)) t)
       ((and cached-pos (= cached-pos (point))) nil)
       ((and cached-pos (> cached-pos (point))
	     (< (abs (- cached-pos (point))) r-lookback-limit))
	(let (end found (here (point)))
	  ; go back to somewhere sure
	  (goto-char cached-pos)
	  (while (> (point) here)
	    ; look for the end of a comment
	    (while (and (if (search-backward comment-end (1- here) 'move)
			    (setq end (match-end 0))
			  (setq end nil))
			(r-in-literal-p)))
	    (if end (setq found (r-backward-comment))))
	  (if (and found (= (point) here)) (setq end nil))
	  (if (not end)
	      (setq r-last-noncomment-pos here)
	    (set-marker r-last-comment-start (point))
	    (set-marker r-last-comment-end end))
	  end))	    
       (t
	(let (begin found (here (point)))
	  ; go back to somewhere sure (or far enough)
	  (goto-char
	   (if cached-pos cached-pos (- (point) r-lookback-limit)))
	  (while (< (point) here)
	    ; look for the beginning of a comment
	    (while (and (if (search-forward comment-start (1+ here) 'move)
			    (setq begin (match-beginning 0))
			  (setq begin nil))
			(r-in-literal-p)))
	    (if begin (setq found (r-forward-comment))))
	  (if (and found (= (point) here)) (setq begin nil))
	  (if (not begin)
	      (setq r-last-noncomment-pos here)
	    (set-marker r-last-comment-start begin)
	    (set-marker r-last-comment-end (point)))
	  begin))))))

(defconst r-before-expr-prefix
  (concat "\\<\\(asr\\|begin\\|class\\|do\\(wnto\\)?\\|else"
	  "\\|i\\(f\\|n\\(herit\\|itializer\\)?\\)"
	  "\\|f\\(or\\|un\\(ct\\(ion\\|or\\)\\)?\\)"
	  "\\|l\\(and\\|or\\|s[lr]\\|xor\\)\\|m\\(atch\\|od\\)"
	  "\\|o[fr]\\|parser\\|s\\(ig\\|truct\\)\\|t\\(hen\\|o\\|ry\\)"
	  "\\|w\\(h\\(en\\|ile\\)\\|ith\\)\\)\\>\\|:begin\\>"
	  "\\|[=<>@^|&+-*/$%][!$%*+-./:<=>?@^|~]*\\|:[:=]\\|[[({,;]")

  "Keywords that may appear immediately before an expression.
Used to distinguish it from toplevel let construct.")

(defun r-in-expr-p ()
  (let ((pos (point)) (in-expr t))
    (r-find-kwop
     (concat r-before-expr-prefix "\\|"
	     r-matching-kw-regexp "\\|"
	     (aref r-kwop-regexps r-max-indent-priority)))
    (cond
     ; special case for ;;
     ((and (= (preceding-char) ?\;) (= (following-char) ?\;)))
     ((looking-at r-before-expr-prefix)
      (goto-char (match-end 0))
      (skip-chars-forward " \t\n")
      (while (looking-at "(\\*")
	(forward-char)
	(r-forward-comment)
	(skip-chars-forward " \t\n"))
      (if (<= pos (point)) (setq in-expr nil))))
    (goto-char pos)
    in-expr))

(defun r-at-sexp-close-p ()
  (or (char-equal ?\) (following-char))
      (char-equal ?\] (following-char))
      (char-equal ?} (following-char))))

(defun r-find-kwop (kwop-regexp)
  "Look back for a n keyword or operator matching KWOP-REGEXP.

Ignore occurences inside literals. If found, return a list of two
values: the actual text of the keyword or operator, and a boolean
indicating whether the keyword was one we looked for explicitly
{non-nil}, or on the other hand one of the block-terminating
keywords."
  
  (let ((start-literal (concat "[\"" r-quote-char "]"))
	found kwop)
    (progn
      (while (and (not found)
		  (re-search-backward kwop-regexp nil t))
	(setq kwop (r-match-string 0))
	(cond
	 ((looking-at "(\\*")
	  (backward-char))
	 ((r-in-comment-p)
	  (search-backward "(" nil 'move))
	 ((looking-at start-literal))
	 ((r-in-literal-p)
	  (re-search-backward start-literal))  ;ugly hack
	 ((setq found t)))))
    (if found
	(if (not (string-match "\\`[^|[]|[^]|]?\\'" kwop)) ;arrrrgh!!
	    kwop
	  (forward-char 1) "|") nil)))

;  Association list of indentation values based on governing keywords.
;
;Each element is of the form (KEYWORD OP-TYPE PRIO INDENT). OP-TYPE is
;non-nil for operator-type nodes, which affect indentation in a
;different way from keywords: subsequent lines are indented to the
;actual occurrence of an operator, but relative to the indentation of
;the line where the governing keyword occurs.

(defconst r-no-indent 0)

(defconst r-kwop-alist
  '(
    ("constraint"	nil	0	n-val-indent)
    ("sig" 		nil	1	n-sig-indent)
    ("ana" 		nil	1	n-struct-indent)
    ("fun"		nil	3	n-fun-indent)
    ("eqn"		nil	3	n-fun-indent)
    ("query"		nil	3	n-fun-indent)
    ("ccr"		nil	3	n-fun-indent)
    ("cim"		nil	3	n-fun-indent)
    ("if"		nil	6	n-if-indent)
    ("if-else"		nil	6	n-if-else-indent)
    ("let"		nil	6	n-let-indent)
    ("let-in"		nil	6	n-let-in-indent)
    ("analysis"		nil	0	n-module-indent)
    ("var"		nil	6	n-try-indent)
    ("set"		nil	0	n-type-indent)
    ("lattice"		nil	0	n-type-indent)
    ("val"		nil	0	n-val-indent)
    ("<-"		nil	3	n-<--indent)
    ("=>"		nil	2	n-->-indent)
    ("{"		t	8	n-lc-indent)
    ("\("		t	8	n-lp-indent)
    ("|"		nil	2	n-no-indent))
; if-else and let-in are not keywords but idioms
; "|" is not in the regexps
; all these 3 values correspond to hard-coded names

"Association list of indentation values based on governing keywords.

Each element is of the form (KEYWORD OP-TYPE PRIO INDENT). OP-TYPE is
non-nil for operator-type nodes, which affect indentation in a
different way from keywords: subsequent lines are indented to the
actual occurrence of an operator, but relative to the indentation of
the line where the governing keyword occurs.")

;;Originally, we had r-kwop-regexp create these at runtime, from an
;;additional field in r-kwop-alist. That proved way too slow,
;;although I still can't understand why. itz

(defconst r-kwop-regexps (make-vector 9 nil)
  "Array of regexps representing n keywords of different priorities.")

(aset r-kwop-regexps 0
      (concat 
       "\\<\\(\\|sig\\|ana\\)\\>"))
(aset r-kwop-regexps 1
      (concat (aref r-kwop-regexps 0) "\\|\\<\\(analysis\\)\\>"))
(aset r-kwop-regexps 2
      (concat
       (aref r-kwop-regexps 1)
       "\\|\\<\\(fun\\)?\\|let"
       "\\|val\\)\\>\\|->"))
(aset r-kwop-regexps 3
      (concat (aref r-kwop-regexps 2) "\\|\\<if\\|when\\>"))
(aset r-kwop-regexps 4
      (concat (aref r-kwop-regexps 3) "\\|<-"))
(aset r-kwop-regexps 5
      (concat (aref r-kwop-regexps 4) "\\|@"))
(aset r-kwop-regexps 6
      (concat (aref r-kwop-regexps 5) ""))
(aset r-kwop-regexps 7
      (concat
       (aref r-kwop-regexps 0)
       "\\|\\<\\(constraint\\)"
       "\\|set\\|lattice\\|val\\)\\>"))
(aset r-kwop-regexps 8
      (concat (aref r-kwop-regexps 6)
       "\\|\\<\\(constraint\\)"
       "\\|set\\|lattice\\|val\\)\\>"))

(defun r-find-done-match ()
  (let ((unbalanced 1) (kwop t))
    (while (and (not (= 0 unbalanced)) kwop)
      (setq kwop (r-find-kwop "\\<\\(done\\|for\\|while\\)\\>"))
      (cond
       ((not kwop))
       ((string= kwop "done") (setq unbalanced (1+ unbalanced)))
       (t (setq unbalanced (1- unbalanced)))))
    kwop))
      
(defun r-find-end-match ()
  (let ((unbalanced 1) (kwop t))
    (while (and (not (= 0 unbalanced)) kwop)
      (setq kwop
	    (r-find-kwop
	     "\\<\\(end\\|sig\\|ana\\)\\>"))
      (cond
       ((not kwop))
       ((string= kwop ";;") (setq kwop nil) (forward-line 1))
       ((string= kwop "end") (setq unbalanced (1+ unbalanced)))
       ( t (setq unbalanced (1- unbalanced)))))
    (if (string= kwop ":begin") "begin"
      kwop)))

(defun r-find-in-match ()
  (let ((unbalanced 1) (kwop t))
    (while (and (not (= 0 unbalanced)) kwop)
      (setq kwop (r-find-kwop "\\<\\(in\\|let\\)\\>"))
      (cond
       ((not kwop))
       ((string= kwop "in") (setq unbalanced (1+ unbalanced)))
       ( t (setq unbalanced (1- unbalanced)))))
    kwop))
  
(defun r-find-with-match ()
  (let ((unbalanced 1) (kwop t))
    (while (and (not (= 0 unbalanced)) kwop)
      (setq kwop
	    (r-find-kwop
	     "\\<\\|try\\>\\|{\\|}"))
      (cond
       ((not kwop))
       ((or (string= kwop "analysis") (string= kwop "analysis"))
	(setq unbalanced 0))
       ((or (string= kwop "with") (string= kwop "}"))
	(setq unbalanced (1+ unbalanced)))
       (t (setq unbalanced (1- unbalanced)))))
    kwop))

(defun r-find-paren-match (close)
  (let ((unbalanced 1)
	(regexp (cond ((= close ?\)) "[()]")
		      ((= close ?\]) "[][]")
		      ((= close ?\}) "[{}]"))))
    (while (and (> unbalanced 0)
		(r-find-kwop regexp))
      (if (= close (following-char))
	  (setq unbalanced (1+ unbalanced))
	(setq unbalanced (1- unbalanced))))))

(defun r-find-then-match (&optional from-else)
  (let ((bol (if from-else
		 (save-excursion
		   (progn (beginning-of-line) (point)))))
	kwop done matching-fun)
    (while (not done)
      (setq kwop (r-find-kwop
		  "\\<\\(e\\(nd\\|lse\\)\\|done\\|then\\|if\\)\\>\\|[])};]"))
      (cond
       ((not kwop) (setq done t))
       ((r-at-sexp-close-p)
	(r-find-paren-match (following-char)))
       ((string= kwop "if") (setq done t))
       ((string= kwop "then")
	(if (not from-else) (setq kwop (r-find-then-match))))
       ((setq matching-fun (cdr-safe (assoc kwop r-matching-kw-alist)))
	(setq kwop (funcall matching-fun)))
       ((string= kwop "then")
	(if (not from-else) (setq kwop (r-find-then-match))))))
    (if (and bol (>= (point) bol))
	"if-else"
      kwop)))

(defun r-find-pipe-match ()
  (let ((done nil) (kwop)
	(re (concat
	     "\\<\\(try\\|match\\|with\\|function\\|parser\\|type"
	     "\\|e\\(nd\\|lse\\)\\|done\\|then\\|in\\)\\>"
	     "\\|[^[|]|\\|[])}]")))
    (while (not done)
      (setq kwop (r-find-kwop re))
      (cond
       ((not kwop) (setq done t))
       ((looking-at "[^[|]\\(|\\)")
	(goto-char (match-beginning 1))
	(setq kwop "|")
	(setq done t))
       ((r-at-sexp-close-p)
	(r-find-paren-match (following-char)))
       ((string= kwop "with")
	(setq kwop (r-find-with-match))
	(setq done t))
       ((string= kwop "parser")
	(if (re-search-backward "\\<with\\>" (- (point) 5) t)
	    (setq kwop (r-find-with-match)))
	(setq done t))
       ((string= kwop "done") (r-find-done-match))
       ((string= kwop "end") (r-find-end-match))
       ((string= kwop "then") (r-find-then-match))
       ((string= kwop "else") (r-find-else-match))
       ((string= kwop "in") (r-find-in-match))
       (t (setq done t))))
    kwop))

(defun r-find-and-match ()
  (let ((done nil) (kwop))
    (while (not done)
      (setq kwop (r-find-kwop
		  "\\<\\(object\\|exception\\|let\\|type\\|end\\|in\\)\\>"))
      (cond
       ((not kwop) (setq done t))
       ((string= kwop "end") (r-find-end-match))
       ((string= kwop "in") (r-find-in-match))
       (t (setq done t))))
    kwop))

(defun r-find-else-match ()
  (r-find-then-match t))

(defun r-find-semi-match ()
  (r-find-kwop-skipping-blocks 2))

(defun r-find-comma-match ()
  (r-find-kwop-skipping-blocks 3))

(defconst r-matching-kw-regexp
  (concat
   "\\<\\(and\\|do\\(ne\\)?\\|e\\(lse\\|nd\\)\\|in\\|t\\(hen\\|o\\)"
   "\\|with\\)\\>\\|[^[|]|")
  "Regexp used in n mode for skipping back over nested blocks.")

(defconst r-matching-kw-alist
  '(("|" . r-find-pipe-match)
    (";" . r-find-semi-match)
    ("," . r-find-comma-match)
    ("end" . r-find-end-match)
    ("done" . r-find-done-match)
    ("in"  . r-find-in-match)
    ("with" . r-find-with-match)
    ("else" . r-find-else-match)
    ("then" . r-find-then-match)
    ("to" . r-find-done-match)
    ("do" . r-find-done-match)
    ("and" . r-find-and-match))

  "Association list used in n mode for skipping back over nested blocks.")

(defun r-find-kwop-skipping-blocks (prio)
  "Look back for a n keyword matching r-kwop-regexps [PRIO].

 Skip nested blocks."

  (let ((done nil) (kwop nil) (matching-fun)
	(kwop-list (aref r-kwop-regexps prio)))
    (while (not done)
      (setq kwop (r-find-kwop
		  (concat r-matching-kw-regexp
			  (cond ((> prio 3) "\\|[])},;]\\|")
				((> prio 2) "\\|[])};]\\|")
				(t "\\|[])}]\\|"))
			  kwop-list)))
      (cond
       ((not kwop) (setq done t))
       ((r-at-sexp-close-p)
	(r-find-paren-match (following-char)))
       ((and (>= prio 2) (string= kwop "|")) (setq done t))
       ((string= kwop "end") (r-find-end-match))
       ((string= kwop "done") (r-find-done-match))
       ((string= kwop "in")
	(cond ((and (r-find-in-match) (>= prio 2))
	       (setq kwop "let-in")
	       (setq done t))))
       ((and (string= kwop "parser") (>= prio 2)
	     (re-search-backward "\\<with\\>" (- (point) 5) t))
	(setq kwop (r-find-with-match))
	(setq done t))
       ((setq matching-fun (cdr-safe (assoc kwop r-matching-kw-alist)))
	(setq kwop (funcall matching-fun))
	(if (looking-at kwop-list) (setq done t)))
       (t (let* ((kwop-info (assoc kwop r-kwop-alist))
		 (is-op (and (nth 1 kwop-info)
			     ; check that we are not at beginning of line
			     (let ((pos (point)) bti)
			       (back-to-indentation)
			       (setq bti (point))
			       (goto-char pos)
			       (< bti pos)))))
	    (if (and is-op (looking-at 
			    (concat (regexp-quote kwop)
				    "|?[ \t]*\\(\n\\|(\\*\\)")))
		(setq kwop-list
		      (aref r-kwop-regexps (nth 2 kwop-info)))
	      (setq done t))))))
    kwop))

(defun r-compute-basic-indent (prio)
  "Compute indent of current n line, ignoring leading keywords.

Find the `governing node' for current line. Compute desired
indentation based on the node and the indentation alists.
Assumes point is exactly at line indentation.
Does not preserve point."
  
  (let* (in-expr
	 (kwop (cond
		((looking-at "|\\([^]|]\\|\\'\\)")
		 (r-find-pipe-match))
		((and (looking-at r-phrase-start-keywords)
		      (r-in-expr-p))
		 (r-find-end-match))
		((and (looking-at r-matching-kw-regexp)
		      (assoc (r-match-string 0) r-matching-kw-alist))
		 (funcall (cdr-safe (assoc (r-match-string 0)
				      r-matching-kw-alist))))
		((looking-at
		  (aref r-kwop-regexps r-max-indent-priority))
		 (let* ((kwop (r-match-string 0))
			(kwop-info (assoc kwop r-kwop-alist))
			(prio (if kwop-info (nth 2 kwop-info)
				n-max-indent-priority)))
		   (if (and (looking-at (aref r-kwop-regexps 0))
			    (not (looking-at "object"))
			    (r-in-expr-p))
		       (setq in-expr t))
		   (r-find-kwop-skipping-blocks prio)))
		(t
		 (if (and (= prio r-max-indent-priority) (r-in-expr-p))
		     (setq in-expr t))
		 (r-find-kwop-skipping-blocks prio))))
	 (kwop-info (assoc kwop r-kwop-alist))
	 (indent-diff
	  (cond
	   ((not kwop-info) (beginning-of-line 1) 0)
	   ((looking-at "[[({][|<]?[ \t]*")
	    (length (r-match-string 0)))
	   ((nth 1 kwop-info) (symbol-value (nth 3 kwop-info)))
	   (t 
	    (let ((pos (point)))
	      (back-to-indentation)
;	      (if (looking-at "\\<let\\>") (goto-char pos))
	      (- (symbol-value (nth 3 kwop-info))
		 (if (looking-at "|") r-|-extra-indent 0))))))
	 (extra (if in-expr r-apply-extra-indent 0)))
	 (+ indent-diff extra (current-column))))

(defconst r-leading-kwops-regexp
  (concat
   "\\<\\(and\\|do\\(ne\\)?\\|e\\(lse\\|nd\\)\\|in"
   "\\|t\\(hen\\|o\\)\\|with\\)\\>\\|[]|})]")

  "Regexp matching n keywords which need special indentation.")

(defconst r-leading-kwops-alist
  '(("and" r-and-extra-indent 2)
    ("do" r-do-extra-indent 0)
    ("done" r-done-extra-indent 0)
    ("else" r-else-extra-indent 3)
    ("end" r-end-extra-indent 0)
    ("in" r-in-extra-indent 2)
    ("then" r-then-extra-indent 3)
    ("to" r-to-extra-indent 0)
    ("with" r-with-extra-indent 2)
    ("|" r-|-extra-indent 2)
    ("]" r-rb-extra-indent 0)
    ("}" r-rc-extra-indent 0)
    (")" r-rp-extra-indent 0))

  "Association list of special n keyword indent values.

Each member is of the form (KEYWORD EXTRA-INDENT PRIO) where
EXTRA-INDENT is the variable holding extra indentation amount for
KEYWORD (usually negative) and PRIO is upper bound on priority of
matching nodes to determine KEYWORD's final indentation.")

(defun r-compute-final-indent ()
  (save-excursion
    (back-to-indentation)
    (cond
     ((looking-at comment-start-skip)
      (current-column))
     ((r-in-comment-p)
      (let ((closing (looking-at "\\*)")))
	(r-backward-comment)
	(looking-at comment-start-skip)
	(+ (current-column)
	   (if closing 0 r-comment-indent))))
     (t (let* ((leading (looking-at r-leading-kwops-regexp))
	       (assoc-val (if leading (assoc (r-match-string 0)
					     r-leading-kwops-alist)))
	       (extra (if leading (symbol-value (nth 1 assoc-val)) 0))
	       (prio (if leading (nth 2 assoc-val)
		       r-max-indent-priority))
	       (basic (r-compute-basic-indent prio)))
	  (max 0 (if extra (+ extra basic) (current-column))))))))
		    


(defun r-split-string ()
  "Called whenever a line is broken inside a n string literal."
  (insert-before-markers "\"^\"")
  (backward-char 1))

(defadvice indent-new-comment-line (around
				    r-indent-new-comment-line
				    activate)
  
  "Handle multi-line strings in n mode."

;this advice doesn't make sense in other modes. I wish there were a
;cleaner way to do this: I haven't found one.

  (let ((hooked (and (eq major-mode 'r-mode) (r-in-literal-p)))
	(split-mark))
    (if (not hooked) nil
      (setq split-mark (set-marker (make-marker) (point)))
      (r-split-string))
    ad-do-it
    (if (not hooked) nil
      (goto-char split-mark)
      (set-marker split-mark nil))))  
  
(defadvice newline-and-indent (around
			       r-newline-and-indent
			       activate)

  "Handle multi-line strings in n mode."

    (let ((hooked (and (eq major-mode 'r-mode) (r-in-literal-p)))
	(split-mark))
    (if (not hooked) nil
      (setq split-mark (set-marker (make-marker) (point)))
      (r-split-string))
    ad-do-it
    (if (not hooked) nil
      (goto-char split-mark)
      (set-marker split-mark nil))))

(defun r-electric-pipe ()
  "If inserting a | or } operator at beginning of line, reindent the line.

Unfortunately there is a situation where this mechanism gets
confused. It's when | is the first character of a |] sequence. This is
a misfeature of n syntax and cannot be fixed, however, as a
workaround, the electric ] inserts | itself if the matching [ is
followed by |."
  
  (interactive "*")
  (let ((electric (and r-electric-indent
		       (r-in-indentation)
		       (not (r-in-comment-p)))))
    (self-insert-command 1)
    (if electric
	(let ((indent
	       (save-excursion
		 (backward-char 1)
		 (r-indent-command)
		 (current-column))))
	  (indent-to (- indent
			(symbol-value
			 (nth 1 (assoc
				 (char-to-string last-command-char)
				 r-leading-kwops-alist)))))))))

(defun r-electric-rb ()
  "If inserting a ] operator at beginning of line, reindent the line.

Also, if the matching [ is followed by a | and this ] is not preceded
by |, insert one."

  (interactive "*")
  (let* ((prec (preceding-char))
	 (look-pipe (and r-electric-close-vector
			 (not (r-in-comment-p))
			 (not (r-in-literal-p))
			 (or (not (numberp prec))
			     (not (char-equal ?| prec)))
			 (set-marker (make-marker) (point))))
	 (electric (and r-electric-indent
			(r-in-indentation)
			(not (r-in-comment-p)))))
    (self-insert-command 1)
    (if electric
	(let ((indent
	       (save-excursion
		 (backward-char 1)
		 (r-indent-command)
		 (current-column))))
	  (indent-to (- indent
			(symbol-value
			 (nth 1 (assoc
				 (char-to-string last-command-char)
				 r-leading-kwops-alist)))))))
    (if look-pipe
	(save-excursion
	  (let ((insert-pipe
		 (condition-case nil
		     (prog2
		       (backward-list 1)
		       (if (looking-at "\\[|") "|" ""))
		   (error ""))))
	    (goto-char look-pipe)
	    (insert insert-pipe))
	  (set-marker look-pipe nil)))))		 

(defun r-abbrev-hook ()
  "If inserting a leading keyword at beginning of line, reindent the line."
  ;itz unfortunately we need a special case 
  (if (and (not (r-in-comment-p)) (not (= last-command-char ?_)))
      (let* ((bol (save-excursion (beginning-of-line) (point)))
	     (kw (save-excursion
		   (and (re-search-backward "^[ \t]*\\(\\sw+\\)\\=" bol t)
			(r-match-string 1)))))
	(if kw
	    (let ((indent (save-excursion
			    (goto-char (match-beginning 1))
			    (r-indent-command)
			    (current-column)))
		  (abbrev-correct (if (= last-command-char ?\ ) 1 0)))
	      (indent-to (- indent
			    (or
                             (symbol-value
                              (nth 1
                                   (assoc kw r-leading-kwops-alist)))
                             0)
			    abbrev-correct)))))))

(defun r-indent-phrase ()
  (interactive "*")
  (let ((bounds (r-mark-phrase)))
    (indent-region (car bounds) (cdr bounds) nil)))

(defun r-backward-to-less-indent (&optional n)
  "Move cursor back  N lines with less or same indentation."
  (interactive "p")
  (beginning-of-line 1)
  (if (< n 0) (r-forward-to-less-indent (- n))
    (while (> n 0)
      (let ((i (current-indentation)))
	(forward-line -1)
	(while (or (> (current-indentation) i)
		   (r-in-comment-p)
		   (looking-at
		    (concat "[ \t]*\\(\n\\|" comment-start-skip "\\)")))
	  (forward-line -1)))
      (setq n (1- n))))
  (back-to-indentation))

(defun r-forward-to-less-indent (&optional n)
  "Move cursor back N lines with less or same indentation."
  (interactive "p")
  (beginning-of-line 1)
  (if (< n 0) (r-backward-to-less-indent (- n))
    (while (> n 0)
      (let ((i (current-indentation)))
	(forward-line 1)
	(while (or (> (current-indentation) i)
		   (r-in-comment-p)
		   (looking-at
		    (concat "[ \t]*\\(\n\\|" comment-start-skip "\\)")))
	  (forward-line 1)))
      (setq n (1- n))))
  (back-to-indentation))  

(defun r-insert-begin-form ()
  "Inserts a nicely formatted begin-end form, leaving a mark after end."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and (numberp prec) (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let* ((c (current-indentation)) (i (+ r-begin-indent c)))
    (insert "begin\n\nend")
    (push-mark)
    (indent-line-to c)
    (forward-line -1)
    (indent-line-to i)))

(defun r-insert-for-form ()
  "Inserts a nicely formatted for-do-done form, leaving a mark after do(ne)."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and (numberp prec) (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let* ((c (current-indentation)) (i (+ r-for-indent c)))
    (insert "for  do\n\ndone")
    (push-mark)
    (indent-line-to c)
    (forward-line -1)
    (indent-line-to i)
    (push-mark)
    (beginning-of-line 1)
    (backward-char 4)))
  
(defun r-insert-if-form ()
  "Insert nicely formatted if-then-else form leaving mark after then, else."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and (numberp prec) (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let* ((c (current-indentation)) (i (+ r-if-indent c)))
    (insert "if\n\nthen\n\nelse\n")
    (indent-line-to i)
    (push-mark)
    (forward-line -1)
    (indent-line-to c)
    (forward-line -1)
    (indent-line-to i)
    (push-mark)
    (forward-line -1)
    (indent-line-to c)
    (forward-line -1)
    (indent-line-to i)))

(defun r-insert-match-form ()
  "Insert nicely formatted match-with form leaving mark after with."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and (numberp prec) (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let* ((c (current-indentation)) (i (+ r-match-indent c)))
    (insert "match\n\nwith\n")
    (indent-line-to i)
    (push-mark)
    (forward-line -1)
    (indent-line-to c)
    (forward-line -1)
    (indent-line-to i)))

(defun r-insert-let-form ()
  "Insert nicely formatted let-in form leaving mark after in."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and (numberp prec) (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let* ((c (current-indentation)))
    (insert "let  in\n")
    (indent-line-to c)
    (push-mark)
    (forward-line -1)
    (forward-char (+ c 4))))

(defun r-insert-try-form ()
  "Insert nicely formatted try-with form leaving mark after with."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and (numberp prec) (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let* ((c (current-indentation)) (i (+ r-try-indent c)))
    (insert "try\n\nwith\n")
    (indent-line-to i)
    (push-mark)
    (forward-line -1)
    (indent-line-to c)
    (forward-line -1)
    (indent-line-to i)))

(defun r-insert-while-form ()
  "Insert nicely formatted while-do-done form leaving mark after do, done."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and (numberp prec) (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let* ((c (current-indentation)) (i (+ r-if-indent c)))
    (insert "while  do\n\ndone")
    (push-mark)
    (indent-line-to c)
    (forward-line -1)
    (indent-line-to i)
    (push-mark)
    (beginning-of-line 1)
    (backward-char 4)))

;;; n.el ends here

(provide 'n)
