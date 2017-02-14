
#|

;;; tweetnacl-bindings.lisp -- Foreign function bindings to the tweetnacl
;;; library for Clozure Common Lisp.  See the following links for more info:
;;;
;;; https://tweetnacl.cr.yp.to
;;; https://tweetnacl.cr.yp.to/tweetnacl-20140917.pdf
;;; 
;;; This code requires a slightly modified version of the tweenacl library:
;;; https://github.com/rongarret/tweetnacl
;;;
;;; It also uses Ergolib:
;;; https://github.com/rongarret/ergolib

Copyright (c) by Ron Garret

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

|#

(require :ergolib)
(require :hashlib)
(require :rffi)

; gcc -shared tweetnacl.c test.c -o tweetnacl.so
(add-path (this-directory))
(ff-load "tweetnacl.so")

;;; Secret key encryption

(defff "crypto_secretbox_xsalsa20poly1305_tweet" (:ptr :ptr :uint :ptr :ptr) :int)
(defff "crypto_secretbox_xsalsa20poly1305_tweet_open" (:ptr :ptr :uint :ptr :ptr) :int)

(defun crypto-secretbox (msg key nonce)
  (bb mlen (+ (length msg) 32)
      (assert (= (length key) 32))
      (assert (= (length nonce) 24))
      (with-heap-ivectors ((mv mp mlen) (nv np nonce) (kv kp key) (cv cp mlen))
        (fill mv 0 :start 0 :end 32)
        (replace mv msg :start1 32)
        (bb result (crypto_secretbox_xsalsa20poly1305_tweet cp mp mlen np kp)
            (unless (zerop result) (error "TweetNaCl encryption failed")))
        (slice cv 16))))

(defun crypto-secretbox-open (msg key nonce)
  (bb clen (+ (length msg) 16)
      (assert (= (length key) 32))
      (assert (= (length nonce) 24))
      (with-heap-ivectors ((cv cp clen) (mv mp clen) (nv np nonce) (kv kp key))
        (fill cv 0 :start 0 :end 16)
        (replace cv msg :start1 16)
        (bb result (crypto_secretbox_xsalsa20poly1305_tweet_open mp cp clen np kp)
            (unless (zerop result) (error "TweetNaCl decryption failed")))
        (slice mv 32))))

;;; Diffie hellman

(defff "crypto_scalarmult_curve25519_tweet" (:ptr :ptr :ptr) :void)
(defff "crypto_scalarmult_curve25519_tweet_base" (:ptr :ptr) :void)

(defv basept (append '(9) (n-of 0 31)))

(defun crypto-scalarmult (p n)
  (assert (= (length p) 32))
  (assert (= (length n) 32))
  (with-heap-ivectors ((pv pp p) (nv np n))
    (with-heap-ivector-result (rv rp 32 'u8)
      (crypto_scalarmult_curve25519_tweet rp np pp))))

(defun crypto-scalarmult-base (n)
  (assert (= (length n) 32))
  (with-heap-ivectors ((nv np n))
    (with-heap-ivector-result (rv rp 32 'u8)
      (crypto_scalarmult_curve25519_tweet_base rp np))))

;;; Signatures

(defff "crypto_sign_keypair_from_seed" (:ptr :ptr) :void)
(defff "crypto_sign_ed25519_tweet" (:ptr :ptr :ptr :uint :ptr) :void)
(defff "crypto_sign_ed25519_tweet_open" (:ptr :ptr :ptr :uint :ptr) :int)

(defun tnacl-sig-keypair-from-seed (seed)
  (assert (= (length seed) 32))
  (with-heap-ivector-results ((skv skp 64) (pkv pkp 32))
    (fill skv 0)
    (replace skv seed)
    (crypto_sign_keypair_from_seed pkp skp)))

(defun tnacl-sign (msg sk)
  (bb mlen (length msg)
      smlen (+ mlen 64)
      (with-heap-ivectors ((smv smp smlen) (mv mp msg) (skv skp sk) (smlenv smlenp 8))
        (crypto_sign_ed25519_tweet smp smlenp mp mlen skp)
        (slice smv 0 64))))

(defun tnacl-verify (msg sig pk)
  (bb mlen (length msg)
      smlen (+ mlen 64)
      (with-heap-ivectors ((smv smp (cat sig msg)) (mv mp smlen)
                           (pkv pkp pk) (mlenv mlenp 8))
          (zerop (crypto_sign_ed25519_tweet_open mp mlenp smp smlen pkp)))))

(defff "spk2epk" (:ptr :ptr) :void)

(defun spk-to-epk (spk)
  (with-heap-ivector (spk-v spk-p spk)
    (with-heap-ivector-result (epk-v epk-p 32 'u8)
      (spk2epk epk-p spk-p))))

(defff "crypto_hash_sha512_tweet" (:ptr :ptr :int) :void)

(defun crypto-hash (v)
  (with-heap-ivector (vv vp v)
    (with-heap-ivector-result (rv rp 64 'u8)
      (crypto_hash_sha512_tweet rp vp (length v)))))

(defff "crypto_box_curve25519xsalsa20poly1305_tweet_beforenm" (:ptr :ptr :ptr) :void)

(defun tnacl-dh (esk epk)
  (with-heap-ivectors ((esk-v esk-p esk) (epk-v epk-p epk))
    (with-heap-ivector-result (kv kp 32 'u8)
      (crypto_box_curve25519xsalsa20poly1305_tweet_beforenm kp epk-p esk-p))))

#+NIL
(progn

; Signature test
(bb :mv (sk pk) (tnacl-sig-keypair-from-seed (random-bytes 32))
    msg (random-bytes 128)
    sig (tnacl-sign msg sk)
    (assert (tnacl-verify msg sig pk))
    (setf (ref msg 0) (logxor (ref msg 0) 1))
    (assert (null (tnacl-verify msg sig pk))))

; Encryption test
(bb msg (random-bytes 128)
    nonce (random-bytes 24)
    key (random-bytes 32)
    c (crypto-secretbox msg key nonce)
    (assert (equalp (crypto-secretbox-open c key nonce) msg)))

; Diffie-helman test
(bb sk1 (random-bytes 32)
    sk2 (random-bytes 32)
    pk1 (crypto-scalarmult-base sk1)
    pk2 (crypto-scalarmult-base sk2)
    k1 (crypto-scalarmult pk1 sk2)
    k2 (crypto-scalarmult pk2 sk1)
    k3 (tnacl-dh sk1 pk2)
    k4 (tnacl-dh sk2 pk1)
    (assert (equalp k1 k2))
    (assert (equalp k3 k4)))

)
