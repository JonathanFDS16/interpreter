#lang racket

(require "project4.rkt"
         racket/file
         racket/list
         racket/system
         racket/path
         racket/string)

;; Extract class name from filename
(define (extract-classname path)
  (define file-name (path->string (file-name-from-path path))) ; <-- FIXED
  (define no-ext (substring file-name 0 (- (string-length file-name) 4))) ; remove ".txt"
  (define parts (regexp-match #px"test\\d+([A-Za-z_][A-Za-z0-9_]*)" no-ext))
  (if parts
      (second parts)
      (error "Filename does not match expected pattern: ~a" file-name)))


;; Run tests and print summary
(define (run-tests-from-dir dir-path)
  (define test-files
    (filter (lambda (p) (regexp-match? #px"\\.txt$" (path->string p)))
            (directory-list dir-path #:build? #t)))

  (define pass-count 0)
  (define fail-count 0)

  (for ([test-path (in-list (sort test-files string<? #:key path->string))]
        [idx (in-naturals 1)])
    (printf "=== Running Test ~a: ~a ===\n" idx (path->string test-path))
    (with-handlers ([exn:fail?
                     (lambda (e)
                       (printf "❌ Error: ~a\n\n" (exn-message e))
                       (set! fail-count (add1 fail-count)))])
      (define classname (string->symbol (extract-classname test-path)))
      (define parsed (parser (path->string test-path)))
      (define output (interpret parsed classname))
      (printf "✅ Output: ~a\n\n" output)
      (set! pass-count (add1 pass-count))))

  ;; Final summary
  (printf "=== Test Summary ===\n")
  (printf "✅ Passed: ~a\n" pass-count)
  (printf "❌ Failed: ~a\n" fail-count)
  (printf "Total Tests: ~a\n" (+ pass-count fail-count)))

;; Run it
(run-tests-from-dir "test")

