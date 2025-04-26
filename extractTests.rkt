#lang racket

(require racket/file
         racket/string
         racket/system
         racket/path)

(define (strip-pre-tags text)
  (define cleaned (regexp-replace #px"^<pre>\\s*" text ""))
  (regexp-replace #px"\\s*</pre>$" cleaned ""))

(define (extract-tests html-path output-dir)
  (define html-content (file->string html-path))

  ;; Match full <pre>...</pre> blocks (no capture)
  (define matches (regexp-match* #px"<pre>[\\s\\S]*?</pre>" html-content))

  ;; Create output directory if not exists
  (unless (directory-exists? output-dir)
    (make-directory output-dir))

  ;; Process each block
  (for ([full-match matches]
        [idx (in-naturals 1)])
    (define code (strip-pre-tags full-match))
    (define output-file (build-path output-dir (format "test~a.txt" idx)))
    (call-with-output-file output-file
      (lambda (out)
        (display code out))
      #:exists 'truncate)
    (printf "Saved Test ~a to ~a\n" idx output-file)))

;; Example usage:
(extract-tests "part4tests.html" "tests")
