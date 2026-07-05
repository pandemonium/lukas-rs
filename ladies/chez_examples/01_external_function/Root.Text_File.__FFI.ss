;;    external open_input_file :: Text -> Int
;;    external close_input_file :: Int -> Unit

(define Root-Text_File-__FFI-open_input_file
  (lambda (file-path)
    (open-input-file file-path)))

(define Root-Text_File-__FFI-close_input_file
  (lambda (input-port)
    (close-input-port input-port)))
