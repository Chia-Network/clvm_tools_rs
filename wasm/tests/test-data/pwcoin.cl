(mod (password new_puzhash amount)
     (include *standard-cl-21*) ;; Specify chialisp-21 compilation.

     (defconstant CREATE_COIN 51)

     (defun get-real-password ()
       0x2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824
       )

     (defun check-password (password)
       (let ((password-hash (sha256 password))
             (real-hash (get-real-password)))
         (= password-hash real-hash)
         )
       )

     (if (check-password password)
         (list (list CREATE_COIN new_puzhash amount))
       (x)
       )
     )
