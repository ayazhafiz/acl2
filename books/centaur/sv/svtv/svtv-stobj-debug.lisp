; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "svtv-stobj")
(include-book "debug")
(local (include-book "std/io/base" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))


;; (svtv-cycle-run-fsm-inputs ins phases) produces a set of inputs for the base
;; fsm given the cycle phases and inputs for the cycle fsm.

;; (svtv-fsm-run-input-envs
;;   (take (len (svtv-probealist-outvars probes)) ins)
;;   overrides fsm)
;; produces a set of inputs for the cycle fsm given inputs for the pipeline.



;; svtv-fsm-debug-init was the same as what is now svtv-design-flatten, so omitting
;; ;; BOZO This should be mostly unnecessary once we can access the moddb/aliases
;; ;; from svtv-data directly.  The main thing we're doing is replicating the
;; ;; moddb and aliases for use in the svtv-debug functions.
;; (define svtv-fsm-debug-init ((design design-p)
;;                              &key
;;                              (moddb 'moddb)
;;                              (aliases 'aliases)
;;                              ;; (debugdata 'debugdata)
;;                              )
;;   :guard (modalist-addr-p (design->modalist design))
;;   :returns (mv err
;;                new-moddb
;;                new-aliases
;;                ;; new-debugdata
;;                )
;;   :prepwork ((local (in-theory (enable modscope-local-bound modscope->modidx modscope-okp))))
;;   (b* (((mv err ?assigns ?fixups ?constraints moddb aliases)
;;         (svex-design-flatten design))
;;        ((when err)
;;         (raise "~@0~%" err)
;;         (mv err moddb aliases))
;;        (aliases (aliases-indexed->named aliases (make-modscope-top
;;                                                  :modidx (moddb-modname-get-index
;;                                                           (design->top design) moddb))
;;                                         moddb)))
;;     (mv nil moddb aliases))
;;   ///
;;   (defret moddb-okp-of-<fn>
;;     (implies (not err)
;;              (and (moddb-mods-ok new-moddb)
;;                   (moddb-basics-ok new-moddb))))

;;   (defret modname-of-<fn>
;;     (implies (not err)
;;              (moddb-modname-get-index (design->top design) new-moddb)))

;;   ;; (defret modidx-of-<fn>
;;   ;;   (implies (not err)
;;   ;;            (< (moddb-modname-get-index (design->top design) new-moddb)
;;   ;;               (nfix (nth *moddb->nmods1* new-moddb))))
;;   ;;   :rule-classes :linear)

;;   (defret totalwires-of-<fn>
;;     (implies (not err)
;;              (<= (moddb-mod-totalwires
;;                   (moddb-modname-get-index (design->top design) new-moddb) new-moddb)
;;                  (len new-aliases)))
;;     :rule-classes :linear))


(local (in-theory (disable hons-dups-p)))



(define fsm-debug-writephases ((phasenum natp)
                                    (inalists svex-envlist-p)
                                    (prev-state svex-env-p)
                                    (fsm base-fsm-p)
                                    aliases vcd-wiremap vcd-vals
                                    (p vl-printedlist-p))
  :guard-hints (("goal" :do-not-induct t))
  :guard (and (<= (aliass-length aliases) (vcdwires-length vcd-wiremap))
              (<= (vcdwires-length vcd-wiremap) (4vecs-length vcd-vals))
              (<= (aliass-length aliases) (4vecs-length vcd-vals))
              (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate fsm))))
              (equal (alist-keys prev-state)
                     (svex-alist-keys (base-fsm->nextstate fsm))))
  :returns (mv vcd-vals1
               (p1 vl-printedlist-p)
               (final-state svex-env-p))
  (b* (((when (atom inalists))
        (mv vcd-vals (vl::vl-printedlist-fix p) (svex-env-fix prev-state)))
       ((base-fsm fsm))
       (eval-alist (append (mbe :logic (svex-env-extract (svex-alist-keys fsm.nextstate) prev-state)
                                :exec prev-state)
                           (car inalists)))
       ((mv wirevals next-state)
        (with-fast-alist eval-alist
          (mv (svex-alist-eval fsm.values eval-alist)
              (svex-alist-eval fsm.nextstate eval-alist))))
       (all-wirevals (append (car inalists) wirevals))
       ((mv changes vcd-vals)
        (with-fast-alist all-wirevals
          ;; evaluate aliases and stick values in vcd-vals,
          ;; tracking changes if phase > 0
          (if (zp phasenum)
              (let* ((vcd-vals (svtv-debug-eval-aliases 0 aliases all-wirevals vcd-vals)))
                (mv nil vcd-vals))
          (svtv-debug-eval-aliases-track 0 aliases all-wirevals vcd-vals))))
       ;; print out changed vals (or all if phase = 0)
       (p (if (zp phasenum)
              (vcd-dump-first-snapshot vcd-vals vcd-wiremap p)
            (vcd-dump-delta (* 10 phasenum) changes vcd-vals vcd-wiremap p))))
    (fsm-debug-writephases (1+ (lnfix phasenum))
                                (cdr inalists)
                                next-state
                                fsm 
                                aliases vcd-wiremap vcd-vals p))
  ///
  (defret len-of-fsm-debug-writephases-vcd-vals
    (<= (len vcd-vals)
        (len vcd-vals1))
    :rule-classes :linear))


(define fsm-debug ((ins svex-envlist-p)
                   (initst svex-env-p)
                   (fsm base-fsm-p)
                   &key
                   ((top-mod modname-p) 'nil)
                   ((filename stringp) '"svtv-debug.vcd")
                   (moddb 'moddb)
                   (aliases 'aliases)
                   (vcd-wiremap 'vcd-wiremap)
                   (vcd-vals 'vcd-vals)
                   (state 'state))
  :guard (and (moddb-ok moddb)
              (b* ((modidx (moddb-modname-get-index top-mod moddb)))
                (and modidx
                     (< modidx (moddb->nmods moddb))
                     (<= (moddb-mod-totalwires modidx moddb)
                         (aliass-length aliases))))
              (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate fsm))))
              (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate fsm))))
  :guard-hints (("Goal" :do-not-induct t))
  (b* (((base-fsm fsm))
       (modidx (moddb-modname-get-index top-mod moddb))

       ;; Start VCD creation.  Make the wiremap and the scope structure (from
       ;; which we write out the module hierarchy portion of the VCD file.)
       (vcd-wiremap (resize-vcdwires (aliass-length aliases) vcd-wiremap))
       ((mv scope & vcd-wiremap) (vcd-moddb->scopes "top" modidx 0 0 moddb vcd-wiremap))

       ;; Start accumulating the contents of the VCD file into reverse
       ;; string/char accumulator p.  Print the header into p.
       ((mv date state) (oslib::date))
       (p (vcd-print-header date scope nil))

       ;; Set up the VCD values structure, an array of 4vecs -- these are
       ;; conveniently initialized to Xes
       (vcd-vals (resize-4vecs (vcdwires-length vcd-wiremap) vcd-vals))
       

       ((mv vcd-vals p &)
        (fsm-debug-writephases 0 ins initst fsm
                               aliases vcd-wiremap vcd-vals p))

       ((mv channel state)
        (open-output-channel (mbe :logic (acl2::str-fix filename) :exec filename)
                             :character state))

       ((unless channel)
        (raise "Couldn't write vcd file ~s0~%" filename)
        (mv vcd-wiremap vcd-vals state))

       (state (princ$ (vl::vl-printedlist->string p) channel state))
       (state (close-output-channel channel state)))
    (mv vcd-wiremap vcd-vals state)))


;; (local (defthm no-duplicatesp-when-equal
;;          (implies (and (equal (svex-alist-keys x) (alist-keys y))
;;                        (svex-alist-eval-equiv! x (svtv-fsm->nextstate z))
;;                        (no-duplicatesp-equal (svex-alist-keys (svtv-fsm->nextstate z))))
;;                   (no-duplicatesp-equal (alist-keys y)))))

(defsection no-duplicates-when-keys-equal-data-nextstate
  (local
   (defret no-duplicate-nextstates-when-equal-<fn>
     (implies (and (equal y
                          (svex-alist-keys (base-fsm->nextstate fsm)))
                   (not err))
              (no-duplicatesp-equal y))
     :fn svtv-design-to-fsm))
  
  (defthm no-duplicate-nextstates-of-base-nextstate
    (implies (and (svtv-data$ap svtv-data)
                  (svtv-data$c->phase-fsm-validp svtv-data))
             (no-duplicatesp-equal (svex-alist-keys (base-fsm->nextstate (svtv-data$c->phase-fsm svtv-data)))))
    :hints(("Goal" :in-theory (e/d (svtv-data$ap))))))

(defthm modalist-addr-p-of-svtv-data-design
  (implies (svtv-data$ap svtv-data)
           (svarlist-addr-p (modalist-vars
                             (design->modalist (svtv-data$c->design svtv-data)))))
  :hints(("Goal" :in-theory (enable svtv-data$ap))))



(define svtv-data-debug-phase-fsm ((ins svex-envlist-p)
                                   (initst svex-env-p)
                                   &key
                                   ((filename stringp) '"svtv-debug.vcd")
                                   (svtv-data 'svtv-data)
                                   (moddb 'moddb)
                                   (aliases 'aliases)
                                   (vcd-wiremap 'vcd-wiremap)
                                   (vcd-vals 'vcd-vals)
                                   (state 'state))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable svtv-data$ap)
  ;;                      :do-not-induct t)))
  (b* ((design (svtv-data->design svtv-data))
       ((mv err ?flatten moddb aliases) (svtv-design-flatten design))
       ((when err)
        (mv err moddb aliases vcd-wiremap vcd-vals state))
       ((mv vcd-wiremap vcd-vals state)
        (fsm-debug ins initst (svtv-data->phase-fsm svtv-data)
                   :top-mod (design->top design)
                   :filename filename)))
    (mv nil moddb aliases vcd-wiremap vcd-vals state)))


(define svtv-data-debug-cycle-fsm ((ins svex-envlist-p)
                                   (initst svex-env-p)
                                   &key
                                   ((filename stringp) '"svtv-debug.vcd")
                                   (svtv-data 'svtv-data)
                                   (moddb 'moddb)
                                   (aliases 'aliases)
                                   (vcd-wiremap 'vcd-wiremap)
                                   (vcd-vals 'vcd-vals)
                                   (state 'state))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              ;; (svtv-data->cycle-fsm-validp svtv-data)
              (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate (svtv-data->phase-fsm svtv-data)))))
  (b* ((base-ins (svtv-cycle-run-fsm-inputs ins (svtv-data->cycle-phases svtv-data))))
    (svtv-data-debug-phase-fsm base-ins initst :filename filename)))


(defthm svex-alist-keys-of-svtv-data->cycle-nextstate
  (implies (and (svtv-data$ap svtv-data)
                ;; (svtv-data$c->base-fsm-validp svtv-data)
                (svtv-data$c->cycle-fsm-validp svtv-data))
           (equal (svex-alist-keys (base-fsm->nextstate (svtv-data$c->cycle-fsm svtv-data)))
                  (svex-alist-keys (base-fsm->nextstate (svtv-data$c->phase-fsm svtv-data)))))
  :hints(("Goal" :in-theory (enable svtv-data$ap))))

(defthm svex-alist-keys-of-svtv-data->pipeline-initst
  (implies (and (svtv-data$ap svtv-data)
                ;; (svtv-data$c->base-fsm-validp svtv-data)
                ;; (svtv-data$c->cycle-fsm-validp svtv-data)
                (svtv-data$c->pipeline-validp svtv-data))
           (equal (svex-alist-keys (pipeline-setup->initst (svtv-data$c->pipeline-setup svtv-data)))
                  (svex-alist-keys (base-fsm->nextstate (svtv-data$c->cycle-fsm svtv-data)))))
  :hints(("Goal" :in-theory (enable svtv-data$ap svtv-data$c-pipeline-okp))))

(define svtv-data-debug-pipeline ((env svex-env-p)
                               &key
                               ((filename stringp) '"svtv-debug.vcd")
                               (svtv-data 'svtv-data)
                               (moddb 'moddb)
                               (aliases 'aliases)
                               (vcd-wiremap 'vcd-wiremap)
                               (vcd-vals 'vcd-vals)
                               (state 'state))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->cycle-fsm-validp svtv-data)
              ;; (svtv-data->namemap-validp svtv-data)
              (svtv-data->pipeline-validp svtv-data)
              )

  (b* (((acl2::with-fast env))
       ((pipeline-setup setup) (svtv-data->pipeline-setup svtv-data))
       (rename-ins (svex-alistlist-eval setup.inputs env))
       (rename-overrides (svex-alistlist-eval setup.overrides env))
       (initst (svex-alist-eval setup.initst env))
       (outvars (svtv-probealist-outvars setup.probes))
       (len (len outvars))
       (fsm (make-svtv-fsm :base-fsm (svtv-data->cycle-fsm svtv-data)
                           :namemap (svtv-data->namemap svtv-data)))
       (cycle-ins (svtv-fsm-run-input-envs
                   (take len rename-ins)
                   rename-overrides fsm)))
    (svtv-data-debug-cycle-fsm cycle-ins initst :filename filename)))


  
