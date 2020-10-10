;;; crdt.el --- collaborative editing using Conflict-free Replicated Data Types
;;
;; Copyright (C) 2020 Qiantan Hong
;;
;; Author: Qiantan Hong <qhong@mit.edu>
;; Maintainer: Qiantan Hong <qhong@mit.edu>
;; Keywords: collaboration crdt
;;
;; crdt.el is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; crdt.el is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with crdt.el.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:
;; * Algorithm
;;   This packages implements the Logoot split algorithm
;;   André, Luc, et al.  "Supporting adaptable granularity of changes for massive-scale collaborative editing." 9th IEEE International Conference on Collaborative Computing: Networking, Applications and Worksharing.  IEEE, 2013.
;; * Protocol
;;   Text-based version
;;   (it should be easy to migrate to a binary version.  Using text for better debugging for now)
;;   Every message takes the form (type . body)
;;   type can be: insert hello cursor challenge sync
;;   - insert
;;     body takes the form (crdt-id position-hint content)
;;     - position-hint is the buffer position where the operation happens at the site
;;       which generates the operation.  Then we can play the trick that start search
;;       near this position at other sites to speedup crdt-id search
;;     - content is the string to be inserted
;;   - delete
;;     body takes the form (position-hint (crdt-id . length)*)
;;   - cursor
;;     body takes the form
;;          (site-id point-position-hint point-crdt-id mark-position-hint mark-crdt-id)
;;     *-crdt-id can be either a CRDT ID, or
;;       - nil, which means clear the point/mark
;;   - contact
;;     body takes the form
;;          (site-id name address)
;;     when name is nil, clear the contact for this site-id
;;   - hello
;;     This message is sent from client to server, when a client connect to the server.
;;     body takes the form (client-name &optional response)
;;   - challenge
;;     body takes the form (salt)
;;   - sync
;;     This message is sent from server to client to get it sync to the state on the server.
;;     It's always sent after server receives a hello message.
;;     Might be used for error recovery or other optimization in the future.
;;     One optimization I have in mind is let server try to merge all CRDT item into a single
;;     one and try to synchronize this state to clients at best effort.
;;     body takes the form (site-id major-mode content . crdt-id-list)
;;     - site-id is the site ID the server assigned to the client
;;     - major-mode is the major mode used at the server site
;;     - content is the string in the buffer
;;     - crdt-id-list is generated from CRDT--DUMP-IDS


;;; Code:

(defgroup crdt nil
  "Collaborative editing using Conflict-free Replicated Data Types."
  :prefix "crdt-"
  :group 'applications)
(defcustom crdt-ask-for-name t
  "Ask for display name everytime a CRDT session is to be started."
  :type 'boolean)
(defcustom crdt-default-name ""
  "Default display name."
  :type 'string)
(defcustom crdt-ask-for-password t
  "Ask for server password everytime a CRDT server is to be started."
  :type 'boolean)

(require 'cl-lib)

(require 'color)
(defvar crdt-cursor-region-colors
  (let ((n 10))
    (cl-loop for i below n
             for hue by (/ 1.0 n)
             collect (cons
                      (apply #'color-rgb-to-hex
                             (color-hsl-to-rgb hue 0.5 0.5))
                      (apply #'color-rgb-to-hex
                             (color-hsl-to-rgb hue 0.2 0.5))))))

(defun crdt--get-cursor-color (site-id)
  "Get cursor color for SITE-ID."
  (car (nth (mod site-id (length crdt-cursor-region-colors)) crdt-cursor-region-colors)))
(defun crdt--get-region-color (site-id)
  "Get region color for SITE-ID."
  (cdr (nth (mod site-id (length crdt-cursor-region-colors)) crdt-cursor-region-colors)))
(defun crdt--move-cursor (ov pos)
  "Move pseudo cursor overlay OV to POS."
  ;; Hax!
  (let* ((eof (eq pos (point-max)))
         (eol (unless eof (eq (char-after pos) ?\n)))
         (end (if eof pos (1+ pos)))
         (display-string
          (when eof
            (unless (or (eq (point) (point-max))
                        (cl-some (lambda (ov)
                                   (and (eq (overlay-get ov 'category) 'crdt-pseudo-cursor)
                                        (overlay-get ov 'before-string)))
                                 (overlays-in (point-max) (point-max))))
              (propertize " " 'face (overlay-get ov 'face))))))
    (move-overlay ov pos end)
    (overlay-put ov 'before-string display-string)))
(defun crdt--move-region (ov pos mark)
  "Move pseudo marked region overlay OV to mark between POS and MARK."
  (move-overlay ov (min pos mark) (max pos mark)))


;; CRDT IDs are represented by unibyte strings (for efficient comparison)
;; Every two bytes represent a big endian encoded integer
;; For base IDs, last two bytes are always representing site ID
;; Stored strings are BASE-ID:OFFSETs. So the last two bytes represent offset,
;; and second last two bytes represent site ID
(defconst crdt--max-value (lsh 1 16))
;; (defconst crdt--max-value 4)
;; for debug
(defconst crdt--low-byte-mask 255)
(defsubst crdt--get-two-bytes (string index)
  "Get the big-endian encoded integer from STRING starting from INDEX.
INDEX is counted by bytes."
  (logior (lsh (elt string index) 8)
          (elt string (1+ index))))
(defsubst crdt--get-two-bytes-with-offset (string offset index default)
  "Helper function for CRDT--GENERATE-ID.
Get the big-endian encoded integer from STRING starting from INDEX,
but with last two-bytes of STRING (the offset portion) replaced by OFFSET,
and padded infintely by DEFAULT to the right."
  (cond ((= index (- (string-bytes string) 2))
         offset)
        ((< (1+ index) (string-bytes string))
         (logior (lsh (elt string index) 8)
                 (elt string (1+ index))))
        (t default)))

(defsubst crdt--id-offset (id)
  "Get the literal offset integer from ID.
Note that it might deviate from real offset for a character
in the middle of a block."
  (crdt--get-two-bytes id (- (string-bytes id) 2)))
(defsubst crdt--set-id-offset (id offset)
  "Set the OFFSET portion of ID destructively."
  (let ((length (string-bytes id)))
    (aset id (- length 2) (lsh offset -8))
    (aset id (- length 1) (logand offset crdt--low-byte-mask))))
(defsubst crdt--id-replace-offset (id offset)
  "Create and return a new id string by replacing the OFFSET portion from ID."
  (let ((new-id (substring id)))
    (crdt--set-id-offset new-id offset)
    new-id))
(defsubst crdt--id-site (id)
  "Get the site id from ID."
  (crdt--get-two-bytes id (- (string-bytes id) 4)))
(defsubst crdt--generate-id (low-id low-offset high-id high-offset site-id)
  "Generate a new ID between LOW-ID and HIGH-ID.
The generating site is marked as SITE-ID.
Offset parts of LOW-ID and HIGH-ID are overriden by LOW-OFFSET
and HIGH-OFFSET.  (to save two copying from using CRDT--ID-REPLACE-OFFSET)"
  (let* ((l (crdt--get-two-bytes-with-offset low-id low-offset 0 0))
         (h (crdt--get-two-bytes-with-offset high-id high-offset 0 crdt--max-value))
         (bytes (cl-loop for pos from 2 by 2
                         while (< (- h l) 2)
                         append (list (lsh l -8)
                                      (logand l crdt--low-byte-mask))
                         do (setq l (crdt--get-two-bytes-with-offset low-id low-offset pos 0))
                         do (setq h (crdt--get-two-bytes-with-offset high-id high-offset pos crdt--max-value))))
         (m (+ l 1 (random (- h l 1)))))
    (apply #'unibyte-string
           (append bytes (list (lsh m -8)
                               (logand m crdt--low-byte-mask)
                               (lsh site-id -8)
                               (logand site-id crdt--low-byte-mask)
                               0
                               0)))))

;; CRDT-ID text property actually stores a cons of (ID-STRING . END-OF-BLOCK-P)
(defsubst crdt--get-crdt-id-pair (pos &optional obj)
  "Get the (CRDT-ID . END-OF-BLOCK-P) pair at POS in OBJ."
  (get-text-property pos 'crdt-id obj))
(defsubst crdt--get-starting-id (pos &optional obj)
  "Get the CRDT-ID at POS in OBJ."
  (car (crdt--get-crdt-id-pair pos obj)))
(defsubst crdt--end-of-block-p (pos &optional obj)
  "Get the END-OF-BLOCK-P at POS in OBJ."
  (cdr (crdt--get-crdt-id-pair pos obj)))
(defsubst crdt--get-starting-id-maybe (pos &optional obj limit)
  "Get the CRDT-ID at POS in OBJ if POS is no smaller than LIMIT.
Return NIL otherwise."
  (unless (< pos (or limit (point-min)))
    (car (get-text-property pos 'crdt-id obj))))
(defsubst crdt--get-id-offset (starting-id pos &optional obj limit)
  "Get the real offset integer for a character at POS.
Assume the stored literal ID is STARTING-ID."
  (let* ((start-pos (previous-single-property-change (1+ pos) 'crdt-id obj (or limit (point-min)))))
    (+ (- pos start-pos) (crdt--id-offset starting-id))))
(defsubst crdt--get-id (pos &optional obj limit)
  "Get the real CRDT ID at POS."
  (let ((limit (or limit (point-min))))
    (if (< pos limit) ""
      (let* ((starting-id (crdt--get-starting-id pos obj))
             (left-offset (crdt--get-id-offset starting-id pos obj limit)))
        (crdt--id-replace-offset starting-id left-offset)))))

(defsubst crdt--set-id (pos id &optional end-of-block-p obj limit)
  "Set the crdt ID and END-OF-BLOCK-P at POS in OBJ.
Any characters after POS but before LIMIT that used to
have the same (CRDT-ID . END-OF-BLOCK-P) pair are also updated
with ID and END-OF-BLOCK-P."
  (put-text-property pos (next-single-property-change pos 'crdt-id obj (or limit (point-max))) 'crdt-id (cons id end-of-block-p) obj))

(cl-defmacro crdt--with-insertion-information
    ((beg end &optional beg-obj end-obj beg-limit end-limit) &body body)
  "Helper macro to setup some useful variables."
  `(let* ((not-begin (> ,beg ,(or beg-limit '(point-min)))) ; if it's nil, we're at the beginning of buffer
          (left-pos (1- ,beg))
          (starting-id-pair (when not-begin (crdt--get-crdt-id-pair left-pos ,beg-obj)))
          (starting-id (if not-begin (car starting-id-pair) ""))
          (left-offset (if not-begin (crdt--get-id-offset starting-id left-pos ,beg-obj ,beg-limit) 0))
          (not-end (< ,end ,(or end-limit '(point-max))))
          (ending-id (if not-end (crdt--get-starting-id ,end ,end-obj) ""))
          (right-offset (if not-end (crdt--id-offset ending-id) 0))
          (beg ,beg)
          (end ,end)
          (beg-obj ,beg-obj)
          (end-obj ,end-obj)
          (beg-limit ,beg-limit)
          (end-limit ,end-limit))
     ,@body))
(defmacro crdt--split-maybe ()
  '(when (and not-end (eq starting-id (crdt--get-starting-id end end-obj)))
     ;; need to split id block
     (crdt--set-id end (crdt--id-replace-offset starting-id (1+ left-offset))
                   (crdt--end-of-block-p left-pos beg-obj) end-obj end-limit)
     (rplacd (get-text-property left-pos 'crdt-id beg-obj) nil) ;; clear end-of-block flag
     t))

(defsubst crdt--same-base-p (a b)
  (let* ((a-length (string-bytes a))
         (b-length (string-bytes b)))
    (and (eq a-length b-length)
         (let ((base-length (- a-length 2)))
           (eq t (compare-strings a 0 base-length b 0 base-length))))))

(defmacro crdt--defvar-permanent-local (name &optional val docstring)
  `(progn
     (defvar-local ,name ,val ,docstring)
     (put ',name 'permanent-local t)))
(crdt--defvar-permanent-local crdt--local-id nil "Local site-id.")
(crdt--defvar-permanent-local crdt--inhibit-update nil "When set, don't call CRDT--LOCAL-* on change.
This is useful for functions that apply remote change to local buffer,
to avoid recusive calling of CRDT synchronization functions.")
(crdt--defvar-permanent-local crdt--changed-string nil)
(crdt--defvar-permanent-local crdt--last-point nil)
(crdt--defvar-permanent-local crdt--last-mark nil)
(crdt--defvar-permanent-local crdt--overlay-table nil
                              "A hash table that maps SITE-ID to CONSes of the form (CURSOR-OVERLAY . REGION-OVERLAY).")
(crdt--defvar-permanent-local crdt--contact-table nil
                              "A hash table that maps SITE-ID to LISTs of the form (DISPLAY-NAME ADDRESS).")
(crdt--defvar-permanent-local crdt--local-name nil)
(crdt--defvar-permanent-local crdt--user-list-buffer nil)

(defvar crdt-user-list-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") #'crdt-user-list-goto)
    map))
(define-derived-mode crdt-user-list-mode tabulated-list-mode
  "CRDT User List"
  (setq tabulated-list-format [("Display name" 15 t)
                               ("Address" 15 t)
                               ("Port" 7 t)]))
(defun crdt-user-list-goto ()
  (interactive)
  (let ((site-id (tabulated-list-get-id)))
    (switch-to-buffer-other-window crdt--user-list-parent)
    (when site-id
      (goto-char (overlay-start (car (gethash site-id crdt--overlay-table)))))))
(crdt--defvar-permanent-local crdt--user-list-parent nil "Set to the CRDT shared buffer, local in a CRDT-USER-LIST buffer.")
(defun crdt-list-users (&optional crdt-buffer display-buffer)
  "Display a list of active users working on a CRDT-shared buffer CRDT-BUFFER.
If DISPLAY-BUFFER is provided, display the output there. Otherwise use a dedicated
buffer for displaying active users on CRDT-BUFFER."
  (interactive)
  (with-current-buffer (or crdt-buffer (current-buffer))
    (unless crdt-mode
      (error "Not a CRDT shared buffer."))
    (unless display-buffer
      (unless (and crdt--user-list-buffer (buffer-live-p crdt--user-list-buffer))
        (let ((crdt-buffer (current-buffer)))
          (setq crdt--user-list-buffer
                (generate-new-buffer (concat (buffer-name (current-buffer))
                                             " users")))
          (with-current-buffer crdt--user-list-buffer
            (setq crdt--user-list-parent crdt-buffer))))
      (setq display-buffer crdt--user-list-buffer))
    (crdt-refresh-users display-buffer)
    (switch-to-buffer-other-window display-buffer)))
(defun crdt-refresh-users (display-buffer)
  (let ((table crdt--contact-table)
        (local-name crdt--local-name))
    (with-current-buffer display-buffer
      (crdt-user-list-mode)
      (setq tabulated-list-entries nil)
      (push (list crdt--local-id (vector local-name "*myself*" "--")) tabulated-list-entries)
      (maphash (lambda (k v)
                 (push (list k (cl-destructuring-bind (name contact) v
                                 (let ((colored-name (concat name " ")))
                                   (put-text-property 0 (1- (length colored-name))
                                                      'face `(:background ,(crdt--get-region-color k))
                                                      colored-name)
                                   (put-text-property (1- (length colored-name)) (length colored-name)
                                                      'face `(:background ,(crdt--get-cursor-color k))
                                                      colored-name)
                                   (vector colored-name (car contact) (format "%s" (cadr contact))))))
                       tabulated-list-entries))
               table)
      (tabulated-list-init-header)
      (tabulated-list-print))))
(defsubst crdt--refresh-users-maybe ()
  (when (and crdt--user-list-buffer (buffer-live-p crdt--user-list-buffer))
    (crdt-refresh-users crdt--user-list-buffer)))

(defun crdt--local-insert (beg end)
  "To be called after a local insert happened in current buffer from BEG to END.
Returns a list of (insert type) messages to be sent."
  (let (resulting-commands)
    (crdt--with-insertion-information
     (beg end)
     (unless (crdt--split-maybe)
       (when (and not-begin
                  (eq (crdt--id-site starting-id) crdt--local-id)
                  (crdt--end-of-block-p left-pos))
         ;; merge crdt id block
         (let* ((max-offset crdt--max-value)
                (merge-end (min end (+ (- max-offset left-offset 1) beg))))
           (unless (= merge-end beg)
             (put-text-property beg merge-end 'crdt-id starting-id-pair)
             (let ((virtual-id (substring starting-id)))
               (crdt--set-id-offset virtual-id (1+ left-offset))
               (push `(insert ,(base64-encode-string virtual-id) ,beg
                              ,(buffer-substring-no-properties beg merge-end))
                     resulting-commands))
             (setq beg merge-end)))))
     (while (< beg end)
       (let ((block-end (min end (+ crdt--max-value beg))))
         (let ((new-id (crdt--generate-id starting-id left-offset ending-id right-offset crdt--local-id)))
           (put-text-property beg block-end 'crdt-id (cons new-id t))
           (push `(insert ,(base64-encode-string new-id) ,beg
                          ,(buffer-substring-no-properties beg block-end))
                 resulting-commands)
           (setq beg block-end)
           (setq left-offset (1- crdt--max-value)) ; this is always true when we need to continue
           (setq starting-id new-id)))))
    ;; (crdt--verify-buffer)
    (nreverse resulting-commands)))

(defun crdt--find-id (id pos)
  "Find the first position *after* ID.  Start the search from POS."
  (let* ((left-pos (previous-single-property-change (if (< pos (point-max)) (1+ pos) pos)
                                                    'crdt-id nil (point-min)))
         (left-id (crdt--get-starting-id left-pos))
         (right-pos (next-single-property-change pos 'crdt-id nil (point-max)))
         (right-id (crdt--get-starting-id right-pos)))
    (cl-block nil
      (while t
        (cond ((<= right-pos (point-min))
               (cl-return (point-min)))
              ((>= left-pos (point-max))
               (cl-return (point-max)))
              ((and right-id (not (string< id right-id)))
               (setq left-pos right-pos)
               (setq left-id right-id)
               (setq right-pos (next-single-property-change right-pos 'crdt-id nil (point-max)))
               (setq right-id (crdt--get-starting-id right-pos)))
              ((string< id left-id)
               (setq right-pos left-pos)
               (setq right-id left-id)
               (setq left-pos (previous-single-property-change left-pos 'crdt-id nil (point-min)))
               (setq left-id (crdt--get-starting-id left-pos)))
              (t
               ;; will unibyte to multibyte conversion cause any problem?
               (cl-return
                (if (eq t (compare-strings left-id 0 (- (string-bytes left-id) 2)
                                           id 0 (- (string-bytes left-id) 2)))
                    (min right-pos (+ left-pos 1
                                      (- (crdt--get-two-bytes id (- (string-bytes left-id) 2))
                                         (crdt--id-offset left-id))))
                  right-pos))))))))
(defun crdt--remote-insert (message)
  (let ((crdt--inhibit-update t))
    (cl-destructuring-bind (id-base64 position-hint content) message
      (let* ((id (base64-decode-string id-base64))
             (beg (crdt--find-id id position-hint)) end)
        (goto-char beg)
        (insert content)
        (setq end (point))
        (with-silent-modifications
          (crdt--with-insertion-information
           (beg end)
           (let ((base-length (- (string-bytes starting-id) 2)))
             (if (and (eq (string-bytes id) (string-bytes starting-id))
                      (eq t (compare-strings starting-id 0 base-length
                                             id 0 base-length))
                      (eq (1+ left-offset) (crdt--id-offset id)))
                 (put-text-property beg end 'crdt-id starting-id-pair)
               (put-text-property beg end 'crdt-id (cons id t))))
           (crdt--split-maybe))))))
  ;; (crdt--verify-buffer)
  )

(defun crdt--local-delete (beg end)
  (let ((outer-end end))
    (crdt--with-insertion-information
     (beg 0 nil crdt--changed-string nil (length crdt--changed-string))
     (if (crdt--split-maybe)
         (let* ((not-end (< outer-end (point-max)))
                (ending-id (when not-end (crdt--get-starting-id outer-end))))
           (when (and not-end (eq starting-id (crdt--get-starting-id outer-end)))
             (crdt--set-id outer-end (crdt--id-replace-offset starting-id (+ 1 left-offset (length crdt--changed-string))))
             t))
       (crdt--with-insertion-information
        ((length crdt--changed-string) outer-end crdt--changed-string nil 0 nil)
        (crdt--split-maybe)))))
  ;; (crdt--verify-buffer)
  `(delete ,beg ,@ (crdt--dump-ids 0 (length crdt--changed-string) crdt--changed-string t)))
(defun crdt--remote-delete (message)
  (cl-destructuring-bind (position-hint . id-pairs) message
    (dolist (id-pair id-pairs)
      (cl-destructuring-bind (length . id-base64) id-pair
        (let ((id (base64-decode-string id-base64)))
          (while (> length 0)
            (goto-char (1- (crdt--find-id id position-hint)))
            (let* ((end-of-block (next-single-property-change (point) 'crdt-id nil (point-max)))
                   (block-length (- end-of-block (point))))
              (cl-case (cl-signum (- length block-length))
                ((1) (delete-char block-length)
                 (cl-decf length block-length)
                 (crdt--set-id-offset id (+ (crdt--id-offset id) block-length)))
                ((0) (delete-char length)
                 (setq length 0))
                ((-1)
                 (let* ((starting-id (crdt--get-starting-id (point)))
                        (left-offset (crdt--get-id-offset starting-id (point))))
                   (delete-char length)
                   (crdt--set-id (point) (crdt--id-replace-offset starting-id (+ left-offset length))))
                 (setq length 0))))))
        ;; (crdt--verify-buffer)
        ))))

(defun crdt--before-change (beg end)
  (unless crdt--inhibit-update
    (setq crdt--changed-string (buffer-substring beg end))))

(defun crdt--after-change (beg end length)
  (mapc (lambda (ov)
          (when (eq (overlay-get ov 'category) 'crdt-pseudo-cursor)
            (crdt--move-cursor ov beg)))
        (overlays-in beg (min (point-max) (1+ beg))))
  (when crdt--local-id ; CRDT--LOCAL-ID is NIL when a client haven't received the first sync message
    (unless crdt--inhibit-update
      (let ((crdt--inhibit-update t))
        ;; we're only interested in text change
        ;; ignore property only changes
        (save-excursion
          (goto-char beg)
          (unless (and (= length (- end beg)) (looking-at (regexp-quote crdt--changed-string)))
            (widen)
            (with-silent-modifications
              (unless (= length 0)
                (crdt--broadcast-maybe
                 (format "%S" (crdt--local-delete beg end))))
              (unless (= beg end)
                (dolist (message (crdt--local-insert beg end))
                  (crdt--broadcast-maybe
                   (format "%S" message)))))))))))

(defun crdt--remote-cursor (message)
  (cl-destructuring-bind
      (site-id point-position-hint point-crdt-id-base64 mark-position-hint mark-crdt-id-base64) message
    (let ((ov-pair (gethash site-id crdt--overlay-table)))
      (if point-crdt-id-base64
          (let* ((point (crdt--find-id (base64-decode-string point-crdt-id-base64) point-position-hint))
                 (mark (if mark-crdt-id-base64
                           (crdt--find-id (base64-decode-string mark-crdt-id-base64) mark-position-hint)
                         point)))
            (unless ov-pair
              (let ((new-cursor (make-overlay 1 1))
                    (new-region (make-overlay 1 1)))
                (overlay-put new-cursor 'face `(:background ,(crdt--get-cursor-color site-id)))
                (overlay-put new-cursor 'category 'crdt-pseudo-cursor)
                (overlay-put new-region 'face `(:background ,(crdt--get-region-color site-id) :extend t))
                (setq ov-pair (puthash site-id (cons new-cursor new-region)
                                       crdt--overlay-table))))
            (crdt--move-cursor (car ov-pair) point)
            (crdt--move-region (cdr ov-pair) point mark))
        (when ov-pair
          (remhash site-id crdt--overlay-table)
          (delete-overlay (car ov-pair))
          (delete-overlay (cdr ov-pair)))))))

(cl-defun crdt--local-cursor (&optional (lazy t))
  (let ((point (point))
        (mark (when (use-region-p) (mark))))
    (unless (and lazy
                 (eq point crdt--last-point)
                 (eq mark crdt--last-mark))
      (when (or (eq point (point-max)) (eq crdt--last-point (point-max)))
        (mapc (lambda (ov)
                (when (eq (overlay-get ov 'category) 'crdt-pseudo-cursor)
                  (crdt--move-cursor ov (point-max))))
              (overlays-in (point-max) (point-max))))
      (setq crdt--last-point point)
      (setq crdt--last-mark mark)
      (let ((point-id-base64 (base64-encode-string (crdt--get-id (1- point))))
            (mark-id-base64 (when mark (base64-encode-string (crdt--get-id (1- mark))))))
        `(cursor ,crdt--local-id
                 ,point ,point-id-base64 ,mark ,mark-id-base64)))))
(defun crdt--post-command ()
  (let ((cursor-message (crdt--local-cursor)))
    (when cursor-message
      (crdt--broadcast-maybe (format "%S" cursor-message)))))


(defun crdt--dump-ids (beg end object &optional omit-end-of-block-p)
  "Serialize all CRDT ids in OBJECT from BEG to END into a list.
The list contains CONSes of the form (LENGTH CRDT-ID-BASE64 . END-OF-BLOCK-P),
or (LENGTH . CRDT-ID-BASE64) if OMIT-END-OF-BLOCK-P is non-NIL.
in the order that they appears in the document"
  (let (ids (pos end))
    (while (> pos beg)
      (let ((prev-pos (previous-single-property-change pos 'crdt-id object beg)))
        (push (cons (- pos prev-pos)
                    (cl-destructuring-bind (id . eob) (crdt--get-crdt-id-pair prev-pos object)
                      (let ((id-base64 (base64-encode-string id)))
                        (if omit-end-of-block-p id-base64 (cons id-base64 eob)))))
              ids)
        (setq pos prev-pos)))
    ids))
(defun crdt--load-ids (ids)
  "Load the CRDT ids in IDS (generated by CRDT--DUMP-IDS)
into current buffer."
  (let ((pos (point-min)))
    (dolist (id-pair ids)
      (let ((next-pos (+ pos (car id-pair))))
        (put-text-property pos next-pos 'crdt-id
                           (cons (base64-decode-string (cadr id-pair)) (cddr id-pair)))
        (setq pos next-pos)))))
(defun crdt--verify-buffer ()
  "Debug helper function.
Verify that CRDT IDs in a document follows ascending order."
  (let* ((pos (point-min))
         (id (crdt--get-starting-id pos)))
    (cl-block
        (while t
          (let* ((next-pos (next-single-property-change pos 'crdt-id))
                 (next-id (if (< next-pos (point-max))
                              (crdt--get-starting-id next-pos)
                            (cl-return)))
                 (prev-id (substring id)))
            (crdt--set-id-offset id (+ (- next-pos pos) (crdt--id-offset id)))
            (unless (string< prev-id next-id)
              (error "Not monotonic!"))
            (setq pos next-pos)
            (setq id next-id))))))

(crdt--defvar-permanent-local crdt--network-process nil)
(crdt--defvar-permanent-local crdt--network-clients nil)
(crdt--defvar-permanent-local crdt--next-client-id nil)
(cl-defun crdt--broadcast-maybe (message-string &optional (without t))
  "Broadcast or send MESSAGE-STRING.
If CRDT--NETWORK-PROCESS is a server process, broadcast MESSAGE-STRING
to clients except the one of which CLIENT-ID property is EQ to WITHOUT.
If CRDT--NETWORK-PROCESS is a server process, send MESSAGE-STRING
to server unless WITHOUT is NIL."
  ;; (message message-string)
  (if (process-contact crdt--network-process :server)
      (dolist (client crdt--network-clients)
        (when (and (eq (process-status client) 'open)
                   (not (eq (process-get client 'client-id) without)))
          (process-send-string client message-string)
          ;; (run-at-time 1 nil #'process-send-string client message-string)
          ;; ^ quick dirty way to simulate network latency, for debugging
          ))
    (when without
      (process-send-string crdt--network-process message-string)
      ;; (run-at-time 1 nil #'process-send-string crdt--network-process message-string)
      )))
(defun crdt--generate-challenge ()
  (apply #'unibyte-string (cl-loop for i below 32 collect (random 256))))
(defun crdt--greet-client (process)
  (cl-pushnew process crdt--network-clients)
  (let ((client-id (process-get process 'client-id)))
    (unless client-id
      (unless (< crdt--next-client-id crdt--max-value)
        (error "Used up client IDs. Need to implement allocation algorithm."))
      (process-put process 'client-id crdt--next-client-id)
      (setq client-id crdt--next-client-id)
      (cl-incf crdt--next-client-id))
    (process-send-string process (format "%S" `(sync
                                                ,client-id
                                                ,major-mode
                                                ,(buffer-substring-no-properties (point-min) (point-max))
                                                ,@ (crdt--dump-ids (point-min) (point-max) nil))))
    (maphash (lambda (site-id ov-pair)
               (cl-destructuring-bind (cursor-ov . region-ov) ov-pair
                 (let* ((point (overlay-start cursor-ov))
                        (region-beg (overlay-start region-ov))
                        (region-end (overlay-end region-ov))
                        (mark (if (eq point region-beg)
                                  (unless (eq point region-end) region-end)
                                region-beg))
                        (point-id-base64 (base64-encode-string (crdt--get-id (1- point))))
                        (mark-id-base64 (when mark (base64-encode-string (crdt--get-id (1- mark))))))
                   (process-send-string process
                                        (format "%S"
                                                `(cursor ,site-id
                                                         ,point ,point-id-base64 ,mark ,mark-id-base64))))))
             crdt--overlay-table)
    (process-send-string process (format "%S" (crdt--local-cursor nil)))
    (maphash (lambda (k v)
               (process-send-string process (format "%S" `(contact ,k ,@v))))
             crdt--contact-table)
    (process-send-string process
                         (format "%S" `(contact ,crdt--local-id
                                                ,crdt--local-name nil)))
    (let ((contact-message `(contact ,client-id ,(process-get process 'client-name)
                                     ,(process-contact process))))
      (crdt--broadcast-maybe (format "%S" contact-message) client-id)
      (crdt-process-message contact-message nil))))

(cl-defgeneric crdt-process-message (message process))
(cl-defmethod crdt-process-message ((message (head insert)) process)
  (crdt--remote-insert (cdr message))
  (crdt--broadcast-maybe (format "%S" message) (process-get process 'client-id)))
(cl-defmethod crdt-process-message ((message (head delete)) process)
  (crdt--remote-delete (cdr message))
  (crdt--broadcast-maybe (format "%S" message) (process-get process 'client-id)))
(cl-defmethod crdt-process-message ((message (head cursor)) process)
  (crdt--remote-cursor (cdr message))
  (crdt--broadcast-maybe (format "%S" message) (process-get process 'client-id)))
(cl-defmethod crdt-process-message ((message (head sync)) process)
  (unless (crdt--server-p) ; server shouldn't receive this
    (erase-buffer)
    (cl-destructuring-bind (id mode content . ids) (cdr message)
      (if (fboundp mode)
          (unless (eq major-mode mode)
            (funcall mode) ; trust your server...
            (crdt-mode))
        (message "Server uses %s, but not available locally." mode))
      (insert content)
      (setq crdt--local-id id)
      (crdt--load-ids ids)
      (puthash 0 (list nil (process-contact process)) crdt--contact-table))))
(cl-defmethod crdt-process-message ((message (head challenge)) process)
  (unless (crdt--server-p) ; server shouldn't receive this
    (message nil)
    (let ((password (read-passwd
                     (format "Password for %s:%s: "
                             (process-contact crdt--network-process :host)
                             (process-contact crdt--network-process :service)))))
      (crdt--broadcast-maybe (format "%S"
                                     `(hello nil ,(gnutls-hash-mac 'SHA1 password (cadr message))))))))
(cl-defmethod crdt-process-message ((message (head contact)) process)
  (cl-destructuring-bind (site-id display-name address) (cdr message)
    (if display-name
        (puthash site-id (list display-name
                               (or address (cadr (gethash site-id crdt--contact-table))))
                 crdt--contact-table)
      (remhash site-id crdt--contact-table))
    (crdt--refresh-users-maybe)))

(defsubst crdt--server-p ()
  (process-contact crdt--network-process :server))

(defun crdt--network-filter (process string)
  (unless (process-buffer process)
    (set-process-buffer process (generate-new-buffer "*crdt-server*"))
    (set-marker (process-mark process) 1))
  (when (buffer-live-p (process-buffer process))
    (with-current-buffer (process-buffer process)
      (save-excursion
        (goto-char (process-mark process))
        (insert string)
        (set-marker (process-mark process) (point))
        (goto-char (point-min))
        (let (message)
          (while (setq message (ignore-errors (read (current-buffer))))
            ;; (print message)
            (with-current-buffer (process-get process 'crdt-buffer)
              (save-excursion
                (widen)
                (if (or (not (crdt--server-p)) (process-get process 'authenticated))
                    (let ((crdt--inhibit-update t))
                      (crdt-process-message message process))
                  (cl-block nil
                    (when (eq (car message) 'hello)
                      (cl-destructuring-bind (name &optional response) (cdr message)
                        (when (or (not (process-get process 'password)) ; server password is empty
                                  (and response (string-equal response (process-get process 'challenge))))
                          (process-put process 'authenticated t)
                          (process-put process 'client-name name)
                          (crdt--greet-client process)
                          (cl-return))))
                    (let ((challenge (crdt--generate-challenge)))
                      (process-put process 'challenge
                                   (gnutls-hash-mac 'SHA1 (substring (process-get process 'password)) challenge))
                      (process-send-string process (format "%S" `(challenge ,challenge))))))))
            (delete-region (point-min) (point))
            (goto-char (point-min))))))))
(defun crdt--server-process-sentinel (client message)
  (with-current-buffer (process-get client 'crdt-buffer)
    (unless (eq (process-status client) 'open)
      ;; client disconnected
      (setq crdt--network-clients (delete client crdt--network-clients))
      ;; generate a clear cursor message and a clear contact message
      (let* ((client-id (process-get client 'client-id))
             (clear-cursor-message `(cursor ,client-id 1 nil 1 nil))
             (clear-contact-message `(contact ,client-id nil nil)))
        (crdt-process-message clear-cursor-message client)
        (crdt-process-message clear-contact-message client)
        (crdt--refresh-users-maybe)))))
(defun crdt--client-process-sentinel (process message)
  (with-current-buffer (process-get process 'crdt-buffer)
    (unless (eq (process-status process) 'open)
      (crdt-stop-client))))
(defun crdt-serve-buffer (port &optional password name)
  "Share the current buffer on PORT."
  (interactive "nPort: ")
  (crdt-mode)
  (setq crdt--local-id 0)
  (setq crdt--network-clients nil)
  (setq crdt--local-clock 0)
  (setq crdt--next-client-id 1)
  (save-excursion
    (widen)
    (let ((crdt--inhibit-update t))
      (with-silent-modifications
        (crdt--local-insert (point-min) (point-max)))))
  (add-hook 'kill-buffer-hook #'crdt-stop-serve-buffer nil t)
  (unless password
    (setq password
          (when crdt-ask-for-password
            (read-from-minibuffer "Set password (empty for no authentication): "))))
  (unless name
    (when crdt-ask-for-name
      (setq name (read-from-minibuffer "Display name: "))))
  (setq crdt--local-name name)
  (setq crdt--network-process
        (make-network-process
         :name "CRDT Server"
         :server t
         :family 'ipv4
         :host "0.0.0.0"
         :service port
         :filter #'crdt--network-filter
         :sentinel #'crdt--server-process-sentinel
         :plist `(crdt-buffer ,(current-buffer) password
                              ,(when (and password (> (length password) 0)) password)))))
(defsubst crdt--clear-overlay-table ()
  (when crdt--overlay-table
    (maphash (lambda (key pair)
               (delete-overlay (car pair))
               (delete-overlay (cdr pair)))
             crdt--overlay-table)
    (setq crdt--overlay-table nil)))
(defun crdt-stop-serve-buffer ()
  "Stop sharing the current buffer."
  (interactive)
  (if (or (not crdt--network-process)
          (not (process-contact crdt--network-process :server)))
      (message "No CRDT server running on current buffer.")
    (when (process-buffer crdt--network-process)
      (kill-buffer (process-buffer crdt--network-process)))
    (delete-process crdt--network-process)
    (dolist (client crdt--network-clients)
      (when (process-live-p client)
        (delete-process client))
      (when (process-buffer client)
        (kill-buffer (process-buffer client))))
    (setq crdt--network-process nil)
    (setq crdt--network-clients nil)
    (crdt--clear-overlay-table)
    (setq crdt--local-id nil)
    (setq crdt--contact-table nil))
  (crdt-mode 0))
(defun crdt-stop-client ()
  "Stop the CRDT client running on current buffer if any.
Leave the buffer open."
  (interactive)
  (if (or (not crdt--network-process) (process-contact crdt--network-process :server))
      (message "No CRDT client running on current buffer.")
    (when (process-buffer crdt--network-process)
      (kill-buffer (process-buffer crdt--network-process)))
    (delete-process crdt--network-process)
    (setq crdt--network-process nil)
    (crdt--clear-overlay-table)
    (setq crdt--local-id nil)
    (setq crdt--contact-table nil)
    (message "Disconnected from server."))
  (crdt-mode 0))
(defun crdt-connect (address port &optional name)
  "Connect to a CRDT server running at ADDRESS:PORT.
Open a new buffer to display the shared content."
  (interactive "MAddress: \nnPort: ")
  (switch-to-buffer (generate-new-buffer "CRDT Client"))
  (unless name
    (when crdt-ask-for-name
      (setq name (read-from-minibuffer "Display name: "))))
  (setq crdt--local-name name)
  (setq crdt--network-process
        (make-network-process
         :name "CRDT Client"
         :buffer (generate-new-buffer "*crdt-client*")
         :host address
         :family 'ipv4
         :service port
         :filter #'crdt--network-filter
         :sentinel #'crdt--client-process-sentinel
         :plist `(crdt-buffer ,(current-buffer))))
  (crdt-mode)
  (add-hook 'kill-buffer-hook #'crdt-stop-client nil t)
  (process-send-string crdt--network-process
                       (format "%S" `(hello ,name)))
  (insert (format "Connected to server %s:%s, synchronizing..." address port)))
(defun crdt-test-client ()
  (interactive)
  (crdt-connect "127.0.0.1" 1333))
(defun crdt-test-server ()
  (interactive)
  (crdt-serve-buffer 1333))
(defun crdt--install-hooks ()
  (add-hook 'after-change-functions #'crdt--after-change nil t)
  (add-hook 'before-change-functions #'crdt--before-change nil t)
  (add-hook 'post-command-hook #'crdt--post-command nil t))
(defun crdt--uninstall-hooks ()
  (remove-hook 'after-change-functions #'crdt--after-change t)
  (remove-hook 'before-change-functions #'crdt--before-change t)
  (remove-hook 'post-command-hook #'crdt--post-command t))
(define-minor-mode crdt-mode
  "CRDT mode" nil " CRDT" nil
  (if crdt-mode
      (progn
        (setq crdt--overlay-table (make-hash-table))
        (setq crdt--contact-table (make-hash-table))
        (crdt--install-hooks))
    (crdt--uninstall-hooks)
    (when crdt--user-list-buffer
      (kill-buffer crdt--user-list-buffer)
      (setq crdt--user-list-buffer nil))))

(provide 'crdt)
