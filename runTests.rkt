#lang racket

(require "interpreter.rkt"
         racket/file
         racket/list
         racket/system
         racket/path)

(define (run-tests-from-dir dir-path)
  ;; List all files inside the directory
  (define test-files
    (filter (lambda (p) (regexp-match? #px"\\.txt$" (path->string p)))
            (directory-list dir-path #:build? #t)))

  ;; Run each test file
  (for ([test-path (in-list (sort test-files string<? #:key path->string))]
        [idx (in-naturals 1)])
    (printf "=== Running Test ~a: ~a ===\n" idx (path->string test-path))
    (with-handlers ([exn:fail?
                     (lambda (e)
                       (printf "Error: ~a\n\n" (exn-message e)))])
      (define output (interpret (parser (path->string test-path))))
      (printf "Output: ~a\n\n" output))))

(run-tests-from-dir "tests")
