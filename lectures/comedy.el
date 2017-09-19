(defun next-slide-please ()
  (interactive)
  (search-forward "{---")
  (next-line)
  (recenter-top-bottom 0)
)
(global-set-key "§" 'next-slide-please)

(defun previous-slide-please ()
  (interactive)
  (search-backward "{---")
  (previous-line)
  (search-backward "{---")
  (next-line)
  (recenter-top-bottom 0)
)
(global-set-key "±" 'previous-slide-please)

(defun comment-in-agda ()
  (interactive)
  (search-forward "{-+}")
  (backward-delete-char 2)
  (insert-string "(-}")
  (search-forward "{+-}")
  (backward-delete-char 3)
  (insert-string "-)-}")  
  (search-backward "{-(-}")
  (next-line)
  (agda2-load)
)
(global-set-key [?\C-§] 'comment-in-agda)

(defun comment-out-agda ()
  (interactive)
  (search-backward "{-(-}")
  (forward-char 4)
  (backward-delete-char 2)
  (insert-string "+")
  (search-forward "-)-}")
  (backward-delete-char 4)
  (insert-string "+-}")  
  (next-line)
  (agda2-load)
)
(global-set-key [?\M-§] 'comment-out-agda)
