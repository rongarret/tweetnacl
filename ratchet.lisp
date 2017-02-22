#|

ratchet.lisp - A Common Lisp implementation of the Signal double-ratchet
using tweetnacl as the crypto primitives

As specified at: https://whispersystems.org/docs/specifications/doubleratchet/

Copyright 2017 by Ron Garret, released under the MIT license

Requires the following support modules:

https://github.com/rongarret/ergolib
https://github.com/rongarret/tweetnacl

NOTE: this was written to be part of SC4 (https://github.com/Spark-Innovations/SC4)
so some of the design is carried over from that project.

|#

(require :ergolib)
(require :basen)
(pushnew (this-directory) *module-search-path* :test 'equalp)
(require :tweetnacl-bindings)

; This should go in general utilities
(define-method (slot-names (c standard-class))
  (mapcar 'slot-definition-name (class-slots c)))

(define-method (slot-names (o standard-object))
  (slot-names (class-of o)))

(define-method (reset (o standard-object))
  (let ((class (class-of o)))
    (finalize-inheritance class)
    (loop for slot in (slot-names class)
      do (slot-makunbound o slot)))
  (initialize-instance o))

(define-method (reset (d dictionary))
  (for k in (force (keys d)) do (del d k)))

(define-method (equal? x y) (equalp x y))

(define-method (equal? (o1 standard-object) (o2 standard-object))
  (and (eq (class-of o1) (class-of o2))
       (every (fn (slot) (equal? (slot-value o1 slot) (slot-value o2 slot)))
              (slot-names o1))))

(define-method (copy (o standard-object))
  (bb o1 (make-instance (class-of o))
      (for slot in (slot-names o) do (setf (ref o1 slot) (ref o slot)))
      o1))

(define-method (slice! (v vector) start &optional end)
  (bb len (length v)
      start (if (< start 0) (max (+ len start) 0) (min start len))
      end (if (null end) len (min len (if (< end 0) (max (+ len end) start) end)))
      (make-array (- end start) :displaced-to v :displaced-index-offset start)))

(defun integer->n-octets (n cnt &optional (little-endian nil))
  (bb v (integer->octets n)
      len (length v)
      (if (= len cnt) (return v))
      (if (> len cnt) (error "~A will not fit in ~A octets, it needs at least ~A" n cnt len))
      zeros (coerce (n-of 0 (- cnt len)) 'octets)
      v (cat zeros v)
      (if little-endian (reverse v) v)))

(defv z24 (apply 'octets (n-of 0 24)))

(defmacro expect-error (form)
  `(bb err (nth-value 1 (ignore-errors ,form))
       (if err
         (logmsg "Received expected error: ~A"
                 (apply 'fmt (ref err 'ccl::format-control)
                        (ref err 'ccl::format-arguments)))
         (error "Failed to produce expected error for ~A" ',form))))

; Serialize/deserialize

#|
Serialization format is as follows: initial byte is:

 |0|1|2|3|4|5|6|7|
 |type |x| len   |

i.e. three bits of type tag, one "extension bit" and four bits of LENgth.  The semantics
of LEN depends on the value of the extension bit.  If the extension bit is 0 then the
length of the payload is 2^LEN.  If the extension bit is 1 then the length of the payload
is encoded in the following bytes, and the LEN value indicates how many bytes are used.
This allows very compact encoding for the most common values of length, namely powers
of 2 from 0 to 15, while allowing effectively unlimited lengths to be encoded.  Note
that powers of 2 may be encoded in two different ways.

The semantics of the payload depend on the TYPE parameter.  The following types
are recognized:

0 = raw byte vector
1 = big-endian unsigned integer
2 = character string encoded as UTF-8
3 = a list of seralized values (see below)
7 = a serialized object (see below)

Values 4-6 are reserved for future expansion.

Lists are serialized by concanetenating the serialziations of their elements.  The
length parameter of a list indicates the number of elements in the list, not the
length of the serialization.

Objects are serialized differetly from other objects.  The format of the leading
byte of a serialized object is:

 |0|1|2|3|4|5|6|7|
 |  7  | classId |

The classId is an integer indicating the class of the object.  The classId must be
between 0 and 30.  The value of 31 is reserved for future expansion (in case we ever
want to be able to serialize more than 30 different classes.)  The classId is an
index into an ordered list of serializable classes, each of which contains an ordered
list of the names of the class's slots.  An instance is serialized as a list of the
values of its slots, i.e. the values of the slots are serialized and concatenated together.

Obviously this depends crucially on the sending and receiving sides having the exact
same class definitions (i.e. same classes with the same slots in the same order).
To support this, the protocol defines a "checksum" on the serializable classes, called
the serialization hash.  This is a hash over the names of all serializable classes and
the names of their slots (see the code for serlalization-hash for the details).  Before
attempting to communicate serialized objects, two endpoints should insure that their
serialization hashes match.

|#


(defun serialize-length (len)
  (bb len-power-of-2? (zerop (logand len (1- len)))
      loglen (integer-length len)
      loglenlen (integer-length loglen)
      (if (and len-power-of-2? (<= loglenlen 4))
        (octets loglen)
        (cat (octets (logior 16 (ceiling loglen 8)))
             (integer->octets len)))))

(defun set-type-tag (v tag)
  (setf (ref v 0) (logior (ref v 0) (ash tag 5)))
  v)
        
(define-method (serialize (v vector))
  (cat (serialize-length (length v)) v))

(define-method (serialize (i integer))
  (set-type-tag (serialize (integer->octets i)) 1))

(define-method (serialize (s string))
  (set-type-tag (serialize (string->octets s)) 2))

(define-method (serialize (l list))
  (set-type-tag (apply 'cat (serialize-length (length l)) (mapcar 'serialize l)) 3))

(defv $serializable-classes nil)

(defun set-serializable-classes (l)
  (setf $serializable-classes (mapcar 'find-class l)))

(define-method (serialize (o standard-object))
  (bb idx (position (class-of o) $serializable-classes)
      (unless idx (error "~A is not of a serializable class" o))
      (cat (set-type-tag (octets idx) 7)
           (serialize (for slot in (slot-names o) collect (ref o slot))))))

(defun deserialize-list (v cnt)
  (if (zerop cnt)
    (values nil v)
    (bb :mv (fst v) (deserialize v)
        :mv (rst v) (deserialize-list v (1- cnt))
        (values (cons fst rst) v))))

(defun deserialize-object (v)
  (bb idx (logand (ref v 0) #x1F)
      class (ref $serializable-classes idx)
      (unless class (error "Unknown deserialization class index: ~A" idx))
      :mv (slot-values v) (deserialize (slice! v 1))
      slot-names (slot-names class)
      o (make-instance class)
      (for (name value) in (zip slot-names slot-values) do
        (setf (ref o name) value))
      (values o v)))

(defun deserialize (v)
  (bb tag (ref v 0)
      type (ash tag -5)
      (if (= type 7) (return (deserialize-object v)))
      extension-bit (logtest tag #x10)
      lenbits (logand tag 15)
      start (if extension-bit (1+ lenbits) 1)
      len (if extension-bit
            (octets->integer (slice v 1 (1+ lenbits)))
            (ash 1 (1- lenbits)))
      (if (= type 3) (return (deserialize-list (slice! v start) len)))
      end (+ start len)
      data (slice v start end)
      result (ecase type
               (0 data)
               (1 (octets->integer data))
               (2 (octets->string data)))
      (values result (slice! v end))))

; Keys

(defun keys-from-seed (seed)
  (bb seed (slice (sha512 seed) 0 32)
      :mv (ssk spk) (tnacl-sig-keypair-from-seed seed)
      esk (slice (sha512 seed) 0 32)
      (setf (ref esk 0) (logand (ref esk 0) #xF8))
      (setf (ref esk 31) (logior 64 (logand 127 (ref esk 31))))
      epk (crypto-scalarmult-base esk)
      (assert (equalp epk (spk-to-epk spk)))
      (values ssk spk esk epk)))

(define-class sc4-public-key spk epk)

(define-method (id (pk sc4-public-key spk)) (slice (b58 spk) 0 12))

(define-print-method (sc4-public-key) "#<SC4 public key ~A>" (id self))

(define-class sc4-secret-key seed ssk esk pubkeys)

(define-method (id (sk sc4-secret-key pubkeys)) (id pubkeys))

(define-print-method (sc4-secret-key) "#<SC4 secret key ~A>" (id self))

(define-method (pubkeys (k sc4-secret-key pubkeys)) pubkeys)

(defun sc4-key (seed)
  (bb :mv (ssk spk esk epk) (keys-from-seed seed)
      pubkeys (make-sc4-public-key :spk spk :epk epk)
      (make-sc4-secret-key :seed seed :ssk ssk :esk esk :pubkeys pubkeys)))

(defun random-bytes (n)
  (bb bytes (make-array n :element-type 'u8)
      (with-open-file (f "/dev/urandom" :element-type 'u8)
        (read-sequence bytes f))
      bytes))

(defun random-sc4-key () (sc4-key (random-bytes 32)))

; Symmetric encryption

(define-method (encrypt (v vector) key &optional (nonce z24))
  (crypto-secretbox v key nonce))

(define-method (encrypt (s string) key &optional (nonce z24))
  (encrypt (string->octets s) key nonce))

(define-method (decrypt (v vector) key &optional (nonce z24))
  (crypto-secretbox-open v key nonce))

; Signatures

(define-class signature spk thing sig)

(define-method (sign (k sc4-secret-key ssk pubkeys) thing)
  (make-signature :spk (ref pubkeys 'spk) :thing thing :sig (tnacl-sign thing ssk)))

(define-method (verify (s signature spk thing sig))
  (tnacl-verify thing sig spk))

; HKDF

(define-method (xor (v1 sequence) (v2 sequence))
  (map 'vector 'logxor v1 v2))

(defun hmac-sha512 (key msg)
  (if (stringp msg) (setf msg (string-to-bytes msg)))
  (bb ipad (n-of #x5c 64)
      opad (n-of #x36 64)
      k1 (sha512 key)
      ikp (xor ipad k1)
      okp (xor opad k1)
      (sha512 (cat okp (sha512 (cat ikp msg))))))

(defv $appid (string->octets "SC4-V0.1"))

(defun hkdf (ikm &key (cnt 32) (salt #()) (info $appid))
  (bb prk (hmac-sha512 salt ikm)
      tt #()
      bytes (for i in (counter 0 (ceiling cnt 64)) collect
              (setf tt (hmac-sha512 prk (cat tt info (list i)))))
      (slice (reduce 'cat bytes) 0 cnt)))

; X3DH

(define-method (dh (sk sc4-secret-key esk) (pk sc4-public-key epk))
  (tnacl-dh esk epk))

(define-method (dh (sk sc4-secret-key esk) (pk vector))
  (tnacl-dh esk pk))

(define-class sc4-user name
  (idk (random-sc4-key)) (prekey (random-sc4-key)) signed-prekey
  (otpk-dict (->)) (used-otpkids '()))

(define-print-method (sc4-user name) "#<SC4 User ~A>" name)

(define-method (sign-prekey (u sc4-user idk prekey signed-prekey))
  (setf signed-prekey (sign idk (ref* prekey 'pubkeys 'epk))))

(defv $otpk-server (->))

(define-method (provision-otpk (u sc4-user name otpk-dict))
  (bb k (random-sc4-key)
      (setf (ref otpk-dict (id k)) k)
      (push (ref k 'pubkeys) (ref $otpk-server name))))

(defun make-sc4-user (name)
  (bb u (make-instance 'sc4-user :name name)
      (sign-prekey u)
      (dotimes (i 3) (provision-otpk u))
      u))

(define-class key-bundle identity-pk signed-prekey otpk)

(define-method (get-key-bundle (u sc4-user name idk signed-prekey otpk-dict))
  (make-instance 'key-bundle
    :identity-pk (ref idk 'pubkeys)
    :signed-prekey signed-prekey
    :otpk (pop (ref $otpk-server name))))

(define-class x3dh-header idk ek otpkid)

(define-method (x3dh-tx (sender sc4-user idk) (kb key-bundle identity-pk signed-prekey otpk))
  (bb (unless (verify signed-prekey) (error "Invalid prekey signature"))
      (unless otpk (warn "No OTPK available"))
      prekey (ref signed-prekey 'thing)
      ek (random-sc4-key)
      dh1 (dh idk prekey)
      dh2 (dh ek identity-pk)
      dh3 (dh ek prekey)
      hdr (make-x3dh-header :idk (ref idk 'pubkeys) :ek (ref ek 'pubkeys))
      (if (null otpk)
        (return (values (hkdf (cat dh1 dh2 dh3)) hdr))
        (setf (ref hdr 'otpkid) (id otpk)))
      dh4 (dh ek otpk)
      (values (hkdf (cat dh1 dh2 dh3 dh4)) hdr)))

(define-method (x3dh-tx (sender sc4-user) (recipient sc4-user))
  (x3dh-tx sender (get-key-bundle recipient)))

(define-method (x3dh-rx (user sc4-user user.idk prekey otpk-dict used-otpkids)
                        (hdr x3dh-header hdr.idk ek otpkid))
  (bb dh1 (dh prekey hdr.idk)
      dh2 (dh user.idk ek)
      dh3 (dh prekey ek)
      (unless otpkid
        (warn "No OTPK in X3DH header")
        (return (hkdf (cat dh1 dh2 dh3))))
      (if (find otpkid used-otpkids) (error "OTPK ~A previously used" otpkid))
      otpk (ref otpk-dict otpkid)
      (unless otpk (error "OTPK ~A unknown" otpkid))
      (del otpk-dict otpkid)
      (push otpkid used-otpkids)
      dh4 (dh otpk ek)
      (hkdf (cat dh1 dh2 dh3 dh4))))

(define-method (x3dh-rx (user sc4-user) (hdr vector))
  (bb :mv (hdr msg) (deserialize hdr)
      sk (x3dh-rx user hdr)
      (values sk (and msg (crypto-secretbox-open msg sk z24)))))

(bb bob (make-sc4-user 'bob)
    alice (make-sc4-user 'alice)
    :mv (sk1 header) (x3dh-tx alice bob)
    (assert (equalp sk1 (x3dh-rx bob header))))

; Signal ratchet

(defun kdf-rk (k1 k2)
  (bb v (hkdf k1 :salt k2 :cnt 64)
      (values (slice v 0 32) (slice v 32))))

(defun kdf-ck (ck) (kdf-rk "" ck))

(define-class ratchet-header pk pn n)

(define-print-method (ratchet-header pk pn n) "#<Ratchet-header ~A ~A ~A>" pk pn n)

(define-class ratchet-session user dhs dhr rk cks ckr (ns 0) (nr 0) (pn 0) (mskipped (->)))

(define-print-method (ratchet-session user mskipped) 
  "#<Ratchet session ~A ~A skipped>" user (length (keys mskipped)))

(define-method (init-for-tx (rs ratchet-session user dhs dhr rk cks)
                            (sender sc4-user) (recipient-key-bundle key-bundle identity-pk)
                            &optional msg)
  (reset rs)
  (setf user sender)
  (bb :mv (sk hdr) (x3dh-tx user recipient-key-bundle)
      (setf dhs (random-sc4-key)
            dhr identity-pk
            (values rk cks) (kdf-rk sk (dh dhs dhr)))
      (cat (serialize hdr) (and msg (crypto-secretbox msg sk z24)))))

(define-method (init-for-tx (rs ratchet-session) (sender sc4-user) (recipient sc4-user)
                            &optional msg)
  (init-for-tx rs sender (get-key-bundle recipient) msg))

(define-method (init-for-rx (rs ratchet-session user dhs rk)
                            (recipient sc4-user idk) x3dh-header)
  (reset rs)
  (setf user recipient)
  (setf dhs idk)
  (bb :mv (sk msg) (x3dh-rx user x3dh-header)
      (setf rk sk)
      (or msg t)))

; Encrypt

(define-method (ratchet-encrypt (rs ratchet-session dhs cks ns pn)
                                plaintext)
  (bb :mv (new-cks mk) (kdf-ck cks)
      (setf cks new-cks)
      pk (ref dhs 'pubkeys)
      header (make-ratchet-header :pk pk :pn pn :n ns)
      (incf ns)
      (cat (serialize header) (crypto-secretbox plaintext mk z24))))

; Decrypt

(define-method (ratchet-decrypt (rs ratchet-session dhr ckr nr)
                                (hdr ratchet-header pk pn n) ciphertext)
  (aif (try-skipped-messsage-keys rs hdr ciphertext) (return-from ratchet-decrypt it))
  (unless (equal? dhr pk)
    (skip-message-keys rs pn)
    (dh-ratchet rs pk))
  (skip-message-keys rs n)
  (bb :mv (new-ckr mk) (kdf-ck ckr)
      (setf ckr new-ckr)
      (incf nr)
      (crypto-secretbox-open ciphertext mk z24)))

(define-method (ratchet-decrypt (rs ratchet-session) (hdr vector) ciphertext)
  (multiple-value-setq (hdr ciphertext) (deserialize hdr))
  (ratchet-decrypt rs hdr ciphertext))

(defun make-mskipped-key (k n)
  (fmt "~A/~A" (id k) n))

(define-method (try-skipped-messsage-keys (rs ratchet-session mskipped)
                                          (hdr ratchet-header pk pn n) ciphertext)
  (bb k (make-mskipped-key pk n)
      mk (ref mskipped k)
      (when mk
        (del mskipped k)
        (crypto-secretbox-open ciphertext mk z24))))

(define-method (skip-message-keys (rs ratchet-session dhr ckr nr mskipped)
                                  until)
  (if (< (+ nr 10) until) (error "Too many skipped messages"))
  (if (< (+ nr 2) until) (warn "~A skipped messages" (- until nr)))
  (if ckr
    (while (< nr until)
      (bb :mv (new-ckr mk) (kdf-ck ckr)
          (setf ckr new-ckr)
          (setf (ref mskipped (make-mskipped-key dhr nr)) mk)
          (incf nr)))))

(define-method (dh-ratchet (rs ratchet-session dhs dhr rk cks ckr ns nr pn) pk)
  (setf pn ns
        ns 0
        nr 0
        dhr pk
        (values rk ckr) (kdf-rk rk (dh dhs dhr))
        dhs (random-sc4-key)
        (values rk cks) (kdf-rk rk (dh dhs dhr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Tests
;;;

; Signatures
(bb thing (random-bytes 32)
    sk (random-sc4-key)
    sig (sign sk thing)
    (assert (verify sig)))

; Symmetric encryption
(bb msg (random-bytes (random 32))
    key (random-bytes 32)
    (assert (equalp msg (decrypt (encrypt msg key) key))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Ratchet demo
;;;

; Setup

(set-serializable-classes
 '(sc4-public-key x3dh-header ratchet-header signature))

(defun serialization-hash ()
  (bb l (for c in $serializable-classes collect
          (cons (class-name c) (slot-names c)))
      s (substitute #\_ #\- (string-downcase (princ-to-string l)))
      (values (b58 (slice (sha512 s) 0 16)) s)))

(assert (equal (serialization-hash) "5RP6tvVXwTsCPsUMid9AMx"))

; Set up users and corresponding ratchet sessions

(defv alice (make-sc4-user 'alice))
(defv bob (make-sc4-user 'bob))
(defv charlie (make-sc4-user 'charlie))

(defv rsa (make-ratchet-session))
(defv rsb (make-ratchet-session))
(defv rsc (make-ratchet-session))

; Reset and provision the OTPK server
(reset $otpk-server)
(provision-otpk bob)

; Alice initiates a session with Bob
(defv hdr nil)
(setf hdr (init-for-tx rsa alice bob #(1 2 3)))
(init-for-rx rsb bob hdr)
(expect-error (init-for-rx rsb bob hdr))
(expect-error (init-for-rx rsc charlie hdr))

; Recover from the intentionally induced error above
(provision-otpk bob)
(setf hdr (init-for-tx rsa alice bob #(1 2 3)))
(init-for-rx rsb bob hdr)

; Drain the otpk supply
(while (ref (get-key-bundle bob) 'otpk))
(setf hdr (init-for-tx rsa alice bob #(1 2 3)))
(init-for-rx rsb bob hdr)

; Encrypted communications
(setf l1 (ratchet-encrypt rsa #(1 2 3 4)))
(ratchet-decrypt rsb l1 nil)

(setf l2 (ratchet-encrypt rsa #(5 6 7 8)))
(setf l3 (ratchet-encrypt rsa #(9 10 11 12)))

(setf l4 (ratchet-encrypt rsb #(13 14 15 16)))

(ratchet-decrypt rsb l3 nil)
(ratchet-decrypt rsb l2 nil)
(ratchet-decrypt rsa l4 nil)

(defun random-sequence () (random-bytes (random 32)))

(dotimes (i 5)
  (bb l (for i in (counter 0 12) collect (ratchet-encrypt rsa (random-sequence)))
      (expect-error (ratchet-decrypt rsb (1st (last l)) nil))
      (for msg in l do (ratchet-decrypt rsb msg nil))
      (setf l (for i in (counter 0 9) collect (ratchet-encrypt rsa (random-sequence))))
      (for msg in (reverse l) do (ratchet-decrypt rsb msg nil))
      ))
