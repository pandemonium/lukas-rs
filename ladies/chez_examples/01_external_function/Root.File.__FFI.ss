;;    external open_input_file :: Text -> Int
;;    external close_input_file :: Int -> Unit

(define Root-File-__FFI-open_file_input_port
  (lambda (file-path)
    (open-input-file file-path)))

(define Root-File-__FFI-get_string_all
  (lambda (file-path)
    (get-string-all file-path)))

(define Root-File-__FFI-close_port
  (lambda (input-port)
    (close-port input-port)))
