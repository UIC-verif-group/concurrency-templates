From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "giveup.c".
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_cls : ident := $"__builtin_cls".
Definition ___builtin_clsl : ident := $"__builtin_clsl".
Definition ___builtin_clsll : ident := $"__builtin_clsll".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition _acquire : ident := $"acquire".
Definition _atom_int : ident := $"atom_int".
Definition _c : ident := $"c".
Definition _css : ident := $"css".
Definition _exit : ident := $"exit".
Definition _findNext : ident := $"findNext".
Definition _get_key : ident := $"get_key".
Definition _get_root : ident := $"get_root".
Definition _get_value : ident := $"get_value".
Definition _hash : ident := $"hash".
Definition _idx : ident := $"idx".
Definition _inRange : ident := $"inRange".
Definition _insertOp : ident := $"insertOp".
Definition _insertOp_helper : ident := $"insertOp_helper".
Definition _key : ident := $"key".
Definition _lock : ident := $"lock".
Definition _lockp : ident := $"lockp".
Definition _lockp__1 : ident := $"lockp__1".
Definition _lockp__2 : ident := $"lockp__2".
Definition _lookupOp_helper : ident := $"lookupOp_helper".
Definition _lookup_md : ident := $"lookup_md".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _make_css : ident := $"make_css".
Definition _makelock : ident := $"makelock".
Definition _malloc : ident := $"malloc".
Definition _max : ident := $"max".
Definition _md : ident := $"md".
Definition _md__1 : ident := $"md__1".
Definition _md__2 : ident := $"md__2".
Definition _md_entry : ident := $"md_entry".
Definition _metadata : ident := $"metadata".
Definition _min : ident := $"min".
Definition _n : ident := $"n".
Definition _new_css : ident := $"new_css".
Definition _new_node : ident := $"new_node".
Definition _node : ident := $"node".
Definition _p : ident := $"p".
Definition _pn : ident := $"pn".
Definition _pn__2 : ident := $"pn__2".
Definition _printDS : ident := $"printDS".
Definition _printDS_helper : ident := $"printDS_helper".
Definition _printf : ident := $"printf".
Definition _ptr_value : ident := $"ptr_value".
Definition _r : ident := $"r".
Definition _release : ident := $"release".
Definition _root : ident := $"root".
Definition _status : ident := $"status".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _t : ident := $"t".
Definition _tgt : ident := $"tgt".
Definition _traverse : ident := $"traverse".
Definition _v : ident := $"v".
Definition _value : ident := $"value".
Definition _x : ident := $"x".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 85) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 84) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_surely_malloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (tulong :: nil) (tptr tvoid) cc_default))
      ((Etempvar _n tulong) :: nil))
    (Sset _p (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tvoid)) tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Sreturn (Some (Etempvar _p (tptr tvoid))))))
|}.

Definition f_hash := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_ptr_value, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr tvoid))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Sset _ptr_value (Ecast (Etempvar _p (tptr tvoid)) tulong))
    (Sreturn (Some (Ecast
                     (Ebinop Omod
                       (Ebinop Omul (Etempvar _ptr_value tulong)
                         (Econst_long (Int64.repr 654435761) tulong) tulong)
                       (Econst_int (Int.repr 16384) tint) tulong) tint)))))
|}.

Definition f_inRange := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_m, (tptr (Tstruct _md_entry noattr))) :: (_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'3, tint) :: (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _m (tptr (Tstruct _md_entry noattr)))
          (Tstruct _md_entry noattr)) _min tint))
    (Sifthenelse (Ebinop Ogt (Etempvar _x tint) (Etempvar _t'2 tint) tint)
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _m (tptr (Tstruct _md_entry noattr)))
              (Tstruct _md_entry noattr)) _max tint))
        (Sset _t'1
          (Ecast (Ebinop Olt (Etempvar _x tint) (Etempvar _t'3 tint) tint)
            tbool)))
      (Sset _t'1 (Econst_int (Int.repr 0) tint))))
  (Sifthenelse (Etempvar _t'1 tint)
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_lookup_md := {|
  fn_return := (tptr (Tstruct _md_entry noattr));
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _css noattr))) ::
                (_p, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr (Tstruct _md_entry noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _hash (Tfunction ((tptr tvoid) :: nil) tint cc_default))
    ((Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _css noattr)))
              (Tstruct _css noattr)) _metadata
            (tarray (tptr (Tstruct _md_entry noattr)) 16384))
          (Etempvar _t'1 tint) (tptr (tptr (Tstruct _md_entry noattr))))
        (tptr (Tstruct _md_entry noattr))))
    (Sreturn (Some (Etempvar _t'2 (tptr (Tstruct _md_entry noattr)))))))
|}.

Definition f_traverse := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _css noattr))) ::
                (_pn__2, (tptr (Tstruct _pn noattr))) :: (_x, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_status, tint) :: (_md, (tptr (Tstruct _md_entry noattr))) ::
               (_r, (tptr (Tstruct _node noattr))) ::
               (_p, (tptr (Tstruct _node noattr))) ::
               (_md__1, (tptr (Tstruct _md_entry noattr))) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, (tptr (Tstruct _md_entry noattr))) ::
               (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _md_entry noattr))) ::
               (_t'18, (tptr (Tstruct _node noattr))) ::
               (_t'17, (tptr (Tstruct _atom_int noattr))) ::
               (_t'16, (tptr (Tstruct _node noattr))) ::
               (_t'15, (tptr (Tstruct _atom_int noattr))) ::
               (_t'14, (tptr (Tstruct _atom_int noattr))) ::
               (_t'13, (tptr (Tstruct _node noattr))) ::
               (_t'12, (tptr (Tstruct _node noattr))) ::
               (_t'11, (tptr (Tstruct _atom_int noattr))) ::
               (_t'10, (tptr (Tstruct _node noattr))) ::
               (_t'9, (tptr (Tstruct _node noattr))) ::
               (_t'8, (tptr (Tstruct _atom_int noattr))) ::
               (_t'7, (tptr (Tstruct _atom_int noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _status (Econst_int (Int.repr 2) tint))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'18
          (Efield
            (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
              (Tstruct _pn noattr)) _n (tptr (Tstruct _node noattr))))
        (Scall (Some _t'1)
          (Evar _lookup_md (Tfunction
                             ((tptr (Tstruct _css noattr)) ::
                              (tptr (Tstruct _node noattr)) :: nil)
                             (tptr (Tstruct _md_entry noattr)) cc_default))
          ((Etempvar _c (tptr (Tstruct _css noattr))) ::
           (Etempvar _t'18 (tptr (Tstruct _node noattr))) :: nil)))
      (Sset _md (Etempvar _t'1 (tptr (Tstruct _md_entry noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'17
          (Efield
            (Ederef (Etempvar _md (tptr (Tstruct _md_entry noattr)))
              (Tstruct _md_entry noattr)) _lock
            (tptr (Tstruct _atom_int noattr))))
        (Scall None
          (Evar _acquire (Tfunction
                           ((tptr (Tstruct _atom_int noattr)) :: nil) tvoid
                           cc_default))
          ((Etempvar _t'17 (tptr (Tstruct _atom_int noattr))) :: nil)))
      (Ssequence
        (Ssequence
          (Sset _t'13
            (Efield
              (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                (Tstruct _pn noattr)) _n (tptr (Tstruct _node noattr))))
          (Sifthenelse (Eunop Onotbool
                         (Etempvar _t'13 (tptr (Tstruct _node noattr))) tint)
            (Ssequence
              (Sset _r
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _css noattr)))
                    (Tstruct _css noattr)) _root
                  (tptr (Tstruct _node noattr))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar _hash (Tfunction ((tptr tvoid) :: nil) tint
                                  cc_default))
                    ((Etempvar _r (tptr (Tstruct _node noattr))) :: nil))
                  (Ssequence
                    (Sset _t'16
                      (Efield
                        (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                          (Tstruct _pn noattr)) _n
                        (tptr (Tstruct _node noattr))))
                    (Scall (Some _t'3)
                      (Evar _hash (Tfunction ((tptr tvoid) :: nil) tint
                                    cc_default))
                      ((Etempvar _t'16 (tptr (Tstruct _node noattr))) :: nil))))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                               (Etempvar _t'3 tint) tint)
                  (Sreturn (Some (Econst_int (Int.repr 2) tint)))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                          (Tstruct _pn noattr)) _n
                        (tptr (Tstruct _node noattr)))
                      (Etempvar _r (tptr (Tstruct _node noattr))))
                    (Ssequence
                      (Sset _t'15
                        (Efield
                          (Ederef
                            (Etempvar _md (tptr (Tstruct _md_entry noattr)))
                            (Tstruct _md_entry noattr)) _lock
                          (tptr (Tstruct _atom_int noattr))))
                      (Scall None
                        (Evar _release (Tfunction
                                         ((tptr (Tstruct _atom_int noattr)) ::
                                          nil) tvoid cc_default))
                        ((Etempvar _t'15 (tptr (Tstruct _atom_int noattr))) ::
                         nil)))))))
            (Ssequence
              (Sset _t'14
                (Efield
                  (Ederef (Etempvar _md (tptr (Tstruct _md_entry noattr)))
                    (Tstruct _md_entry noattr)) _lock
                  (tptr (Tstruct _atom_int noattr))))
              (Scall None
                (Evar _release (Tfunction
                                 ((tptr (Tstruct _atom_int noattr)) :: nil)
                                 tvoid cc_default))
                ((Etempvar _t'14 (tptr (Tstruct _atom_int noattr))) :: nil)))))
        (Ssequence
          (Sset _p
            (Efield
              (Ederef (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                (Tstruct _pn noattr)) _n (tptr (Tstruct _node noattr))))
          (Ssequence
            (Sloop
              (Ssequence
                Sskip
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'12
                        (Efield
                          (Ederef
                            (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                            (Tstruct _pn noattr)) _n
                          (tptr (Tstruct _node noattr))))
                      (Scall (Some _t'4)
                        (Evar _lookup_md (Tfunction
                                           ((tptr (Tstruct _css noattr)) ::
                                            (tptr (Tstruct _node noattr)) ::
                                            nil)
                                           (tptr (Tstruct _md_entry noattr))
                                           cc_default))
                        ((Etempvar _c (tptr (Tstruct _css noattr))) ::
                         (Etempvar _t'12 (tptr (Tstruct _node noattr))) ::
                         nil)))
                    (Sset _md__1
                      (Etempvar _t'4 (tptr (Tstruct _md_entry noattr)))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'11
                        (Efield
                          (Ederef
                            (Etempvar _md__1 (tptr (Tstruct _md_entry noattr)))
                            (Tstruct _md_entry noattr)) _lock
                          (tptr (Tstruct _atom_int noattr))))
                      (Scall None
                        (Evar _acquire (Tfunction
                                         ((tptr (Tstruct _atom_int noattr)) ::
                                          nil) tvoid cc_default))
                        ((Etempvar _t'11 (tptr (Tstruct _atom_int noattr))) ::
                         nil)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'10
                          (Efield
                            (Ederef
                              (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                              (Tstruct _pn noattr)) _n
                            (tptr (Tstruct _node noattr))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                              (Tstruct _pn noattr)) _p
                            (tptr (Tstruct _node noattr)))
                          (Etempvar _t'10 (tptr (Tstruct _node noattr)))))
                      (Ssequence
                        (Scall (Some _t'6)
                          (Evar _inRange (Tfunction
                                           ((tptr (Tstruct _md_entry noattr)) ::
                                            tint :: nil) tint cc_default))
                          ((Etempvar _md__1 (tptr (Tstruct _md_entry noattr))) ::
                           (Etempvar _x tint) :: nil))
                        (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tint)
                                       (Econst_int (Int.repr 1) tint) tint)
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'9
                                  (Efield
                                    (Ederef
                                      (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                      (Tstruct _pn noattr)) _p
                                    (tptr (Tstruct _node noattr))))
                                (Scall (Some _t'5)
                                  (Evar _findNext (Tfunction
                                                    ((tptr (Tstruct _node noattr)) ::
                                                     (tptr (tptr (Tstruct _node noattr))) ::
                                                     tint :: nil) tint
                                                    cc_default))
                                  ((Etempvar _t'9 (tptr (Tstruct _node noattr))) ::
                                   (Ecast
                                     (Eaddrof
                                       (Efield
                                         (Ederef
                                           (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                           (Tstruct _pn noattr)) _n
                                         (tptr (Tstruct _node noattr)))
                                       (tptr (tptr (Tstruct _node noattr))))
                                     (tptr (tptr (Tstruct _node noattr)))) ::
                                   (Etempvar _x tint) :: nil)))
                              (Sset _status (Etempvar _t'5 tint)))
                            (Sifthenelse (Ebinop Oeq (Etempvar _status tint)
                                           (Econst_int (Int.repr 0) tint)
                                           tint)
                              Sbreak
                              (Sifthenelse (Ebinop Oeq
                                             (Etempvar _status tint)
                                             (Econst_int (Int.repr 1) tint)
                                             tint)
                                Sbreak
                                (Ssequence
                                  (Sset _t'8
                                    (Efield
                                      (Ederef
                                        (Etempvar _md__1 (tptr (Tstruct _md_entry noattr)))
                                        (Tstruct _md_entry noattr)) _lock
                                      (tptr (Tstruct _atom_int noattr))))
                                  (Scall None
                                    (Evar _release (Tfunction
                                                     ((tptr (Tstruct _atom_int noattr)) ::
                                                      nil) tvoid cc_default))
                                    ((Etempvar _t'8 (tptr (Tstruct _atom_int noattr))) ::
                                     nil))))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'7
                                (Efield
                                  (Ederef
                                    (Etempvar _md__1 (tptr (Tstruct _md_entry noattr)))
                                    (Tstruct _md_entry noattr)) _lock
                                  (tptr (Tstruct _atom_int noattr))))
                              (Scall None
                                (Evar _release (Tfunction
                                                 ((tptr (Tstruct _atom_int noattr)) ::
                                                  nil) tvoid cc_default))
                                ((Etempvar _t'7 (tptr (Tstruct _atom_int noattr))) ::
                                 nil)))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _pn__2 (tptr (Tstruct _pn noattr)))
                                  (Tstruct _pn noattr)) _n
                                (tptr (Tstruct _node noattr)))
                              (Etempvar _p (tptr (Tstruct _node noattr)))))))))))
              Sskip)
            (Sreturn (Some (Etempvar _status tint)))))))))
|}.

Definition f_insertOp_helper := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _css noattr))) ::
                (_p, (tptr (Tstruct _node noattr))) :: (_x, tint) ::
                (_value, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_new_node, (tptr (Tstruct _node noattr))) ::
               (_md, (tptr (Tstruct _md_entry noattr))) ::
               (_lockp, (tptr (Tstruct _atom_int noattr))) :: (_idx, tint) ::
               (_lock, (tptr (Tstruct _atom_int noattr))) ::
               (_md__1, (tptr (Tstruct _md_entry noattr))) ::
               (_lockp__1, (tptr (Tstruct _atom_int noattr))) ::
               (_md__2, (tptr (Tstruct _md_entry noattr))) ::
               (_lockp__2, (tptr (Tstruct _atom_int noattr))) ::
               (_key, tint) :: (_t'8, tint) ::
               (_t'7, (tptr (Tstruct _md_entry noattr))) ::
               (_t'6, (tptr (Tstruct _md_entry noattr))) ::
               (_t'5, (tptr (Tstruct _atom_int noattr))) ::
               (_t'4, (tptr tvoid)) :: (_t'3, tint) ::
               (_t'2, (tptr (Tstruct _md_entry noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) ::
               (_t'17, (tptr (Tstruct _md_entry noattr))) ::
               (_t'16, (tptr (Tstruct _md_entry noattr))) ::
               (_t'15, (tptr (Tstruct _md_entry noattr))) :: (_t'14, tint) ::
               (_t'13, (tptr (Tstruct _md_entry noattr))) ::
               (_t'12, (tptr (Tstruct _md_entry noattr))) ::
               (_t'11, (tptr (Tstruct _md_entry noattr))) :: (_t'10, tint) ::
               (_t'9, (tptr (Tstruct _md_entry noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _insertOp (Tfunction
                        ((tptr (Tstruct _node noattr)) :: tint ::
                         (tptr tvoid) :: nil) (tptr (Tstruct _node noattr))
                        cc_default))
      ((Etempvar _p (tptr (Tstruct _node noattr))) :: (Etempvar _x tint) ::
       (Etempvar _value (tptr tvoid)) :: nil))
    (Sset _new_node (Etempvar _t'1 (tptr (Tstruct _node noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _new_node (tptr (Tstruct _node noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _lookup_md (Tfunction
                               ((tptr (Tstruct _css noattr)) ::
                                (tptr (Tstruct _node noattr)) :: nil)
                               (tptr (Tstruct _md_entry noattr)) cc_default))
            ((Etempvar _c (tptr (Tstruct _css noattr))) ::
             (Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
          (Sset _md (Etempvar _t'2 (tptr (Tstruct _md_entry noattr)))))
        (Ssequence
          (Sset _lockp
            (Efield
              (Ederef (Etempvar _md (tptr (Tstruct _md_entry noattr)))
                (Tstruct _md_entry noattr)) _lock
              (tptr (Tstruct _atom_int noattr))))
          (Ssequence
            (Scall None
              (Evar _release (Tfunction
                               ((tptr (Tstruct _atom_int noattr)) :: nil)
                               tvoid cc_default))
              ((Etempvar _lockp (tptr (Tstruct _atom_int noattr))) :: nil))
            (Sreturn None))))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _hash (Tfunction ((tptr tvoid) :: nil) tint cc_default))
          ((Etempvar _new_node (tptr (Tstruct _node noattr))) :: nil))
        (Sset _idx (Etempvar _t'3 tint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _surely_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                   cc_default))
            ((Esizeof (Tstruct _md_entry noattr) tulong) :: nil))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _c (tptr (Tstruct _css noattr)))
                    (Tstruct _css noattr)) _metadata
                  (tarray (tptr (Tstruct _md_entry noattr)) 16384))
                (Etempvar _idx tint)
                (tptr (tptr (Tstruct _md_entry noattr))))
              (tptr (Tstruct _md_entry noattr)))
            (Etempvar _t'4 (tptr tvoid))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _makelock (Tfunction nil
                                (tptr (Tstruct _atom_int noattr)) cc_default))
              nil)
            (Sset _lock (Etempvar _t'5 (tptr (Tstruct _atom_int noattr)))))
          (Ssequence
            (Ssequence
              (Sset _t'17
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _c (tptr (Tstruct _css noattr)))
                        (Tstruct _css noattr)) _metadata
                      (tarray (tptr (Tstruct _md_entry noattr)) 16384))
                    (Etempvar _idx tint)
                    (tptr (tptr (Tstruct _md_entry noattr))))
                  (tptr (Tstruct _md_entry noattr))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _t'17 (tptr (Tstruct _md_entry noattr)))
                    (Tstruct _md_entry noattr)) _lock
                  (tptr (Tstruct _atom_int noattr)))
                (Etempvar _lock (tptr (Tstruct _atom_int noattr)))))
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _p (tptr (Tstruct _node noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _c (tptr (Tstruct _css noattr)))
                        (Tstruct _css noattr)) _root
                      (tptr (Tstruct _node noattr)))
                    (Etempvar _new_node (tptr (Tstruct _node noattr))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'16
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _c (tptr (Tstruct _css noattr)))
                                (Tstruct _css noattr)) _metadata
                              (tarray (tptr (Tstruct _md_entry noattr)) 16384))
                            (Etempvar _idx tint)
                            (tptr (tptr (Tstruct _md_entry noattr))))
                          (tptr (Tstruct _md_entry noattr))))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _t'16 (tptr (Tstruct _md_entry noattr)))
                            (Tstruct _md_entry noattr)) _min tint)
                        (Ebinop Osub
                          (Eunop Oneg (Econst_int (Int.repr 2147483647) tint)
                            tint) (Econst_int (Int.repr 1) tint) tint)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'15
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _c (tptr (Tstruct _css noattr)))
                                  (Tstruct _css noattr)) _metadata
                                (tarray (tptr (Tstruct _md_entry noattr)) 16384))
                              (Etempvar _idx tint)
                              (tptr (tptr (Tstruct _md_entry noattr))))
                            (tptr (Tstruct _md_entry noattr))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _t'15 (tptr (Tstruct _md_entry noattr)))
                              (Tstruct _md_entry noattr)) _max tint)
                          (Econst_int (Int.repr 2147483647) tint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'6)
                            (Evar _lookup_md (Tfunction
                                               ((tptr (Tstruct _css noattr)) ::
                                                (tptr (Tstruct _node noattr)) ::
                                                nil)
                                               (tptr (Tstruct _md_entry noattr))
                                               cc_default))
                            ((Etempvar _c (tptr (Tstruct _css noattr))) ::
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) :: nil))
                          (Sset _md__1
                            (Etempvar _t'6 (tptr (Tstruct _md_entry noattr)))))
                        (Ssequence
                          (Sset _lockp__1
                            (Efield
                              (Ederef
                                (Etempvar _md__1 (tptr (Tstruct _md_entry noattr)))
                                (Tstruct _md_entry noattr)) _lock
                              (tptr (Tstruct _atom_int noattr))))
                          (Ssequence
                            (Scall None
                              (Evar _release (Tfunction
                                               ((tptr (Tstruct _atom_int noattr)) ::
                                                nil) tvoid cc_default))
                              ((Etempvar _lock (tptr (Tstruct _atom_int noattr))) ::
                               nil))
                            (Ssequence
                              (Scall None
                                (Evar _release (Tfunction
                                                 ((tptr (Tstruct _atom_int noattr)) ::
                                                  nil) tvoid cc_default))
                                ((Etempvar _lockp__1 (tptr (Tstruct _atom_int noattr))) ::
                                 nil))
                              (Sreturn None))))))))
                Sskip)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar _lookup_md (Tfunction
                                       ((tptr (Tstruct _css noattr)) ::
                                        (tptr (Tstruct _node noattr)) :: nil)
                                       (tptr (Tstruct _md_entry noattr))
                                       cc_default))
                    ((Etempvar _c (tptr (Tstruct _css noattr))) ::
                     (Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
                  (Sset _md__2
                    (Etempvar _t'7 (tptr (Tstruct _md_entry noattr)))))
                (Ssequence
                  (Sset _lockp__2
                    (Efield
                      (Ederef
                        (Etempvar _md__2 (tptr (Tstruct _md_entry noattr)))
                        (Tstruct _md_entry noattr)) _lock
                      (tptr (Tstruct _atom_int noattr))))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'8)
                        (Evar _get_key (Tfunction
                                         ((tptr (Tstruct _node noattr)) ::
                                          nil) tint cc_default))
                        ((Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
                      (Sset _key (Etempvar _t'8 tint)))
                    (Sifthenelse (Ebinop Olt (Etempvar _x tint)
                                   (Etempvar _key tint) tint)
                      (Ssequence
                        (Ssequence
                          (Sset _t'13
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _c (tptr (Tstruct _css noattr)))
                                    (Tstruct _css noattr)) _metadata
                                  (tarray (tptr (Tstruct _md_entry noattr)) 16384))
                                (Etempvar _idx tint)
                                (tptr (tptr (Tstruct _md_entry noattr))))
                              (tptr (Tstruct _md_entry noattr))))
                          (Ssequence
                            (Sset _t'14
                              (Efield
                                (Ederef
                                  (Etempvar _md__2 (tptr (Tstruct _md_entry noattr)))
                                  (Tstruct _md_entry noattr)) _min tint))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _t'13 (tptr (Tstruct _md_entry noattr)))
                                  (Tstruct _md_entry noattr)) _min tint)
                              (Etempvar _t'14 tint))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'12
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _c (tptr (Tstruct _css noattr)))
                                      (Tstruct _css noattr)) _metadata
                                    (tarray (tptr (Tstruct _md_entry noattr)) 16384))
                                  (Etempvar _idx tint)
                                  (tptr (tptr (Tstruct _md_entry noattr))))
                                (tptr (Tstruct _md_entry noattr))))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _t'12 (tptr (Tstruct _md_entry noattr)))
                                  (Tstruct _md_entry noattr)) _max tint)
                              (Etempvar _key tint)))
                          (Ssequence
                            (Scall None
                              (Evar _release (Tfunction
                                               ((tptr (Tstruct _atom_int noattr)) ::
                                                nil) tvoid cc_default))
                              ((Etempvar _lock (tptr (Tstruct _atom_int noattr))) ::
                               nil))
                            (Scall None
                              (Evar _release (Tfunction
                                               ((tptr (Tstruct _atom_int noattr)) ::
                                                nil) tvoid cc_default))
                              ((Etempvar _lockp__2 (tptr (Tstruct _atom_int noattr))) ::
                               nil)))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'11
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _c (tptr (Tstruct _css noattr)))
                                    (Tstruct _css noattr)) _metadata
                                  (tarray (tptr (Tstruct _md_entry noattr)) 16384))
                                (Etempvar _idx tint)
                                (tptr (tptr (Tstruct _md_entry noattr))))
                              (tptr (Tstruct _md_entry noattr))))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _t'11 (tptr (Tstruct _md_entry noattr)))
                                (Tstruct _md_entry noattr)) _min tint)
                            (Etempvar _key tint)))
                        (Ssequence
                          (Ssequence
                            (Sset _t'9
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _c (tptr (Tstruct _css noattr)))
                                      (Tstruct _css noattr)) _metadata
                                    (tarray (tptr (Tstruct _md_entry noattr)) 16384))
                                  (Etempvar _idx tint)
                                  (tptr (tptr (Tstruct _md_entry noattr))))
                                (tptr (Tstruct _md_entry noattr))))
                            (Ssequence
                              (Sset _t'10
                                (Efield
                                  (Ederef
                                    (Etempvar _md__2 (tptr (Tstruct _md_entry noattr)))
                                    (Tstruct _md_entry noattr)) _max tint))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _t'9 (tptr (Tstruct _md_entry noattr)))
                                    (Tstruct _md_entry noattr)) _max tint)
                                (Etempvar _t'10 tint))))
                          (Ssequence
                            (Scall None
                              (Evar _release (Tfunction
                                               ((tptr (Tstruct _atom_int noattr)) ::
                                                nil) tvoid cc_default))
                              ((Etempvar _lock (tptr (Tstruct _atom_int noattr))) ::
                               nil))
                            (Scall None
                              (Evar _release (Tfunction
                                               ((tptr (Tstruct _atom_int noattr)) ::
                                                nil) tvoid cc_default))
                              ((Etempvar _lockp__2 (tptr (Tstruct _atom_int noattr))) ::
                               nil))))))))))))))))
|}.

Definition f_lookupOp_helper := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _css noattr))) ::
                (_p, (tptr (Tstruct _node noattr))) :: (_x, tint) ::
                (_status, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_v, (tptr tvoid)) ::
               (_md, (tptr (Tstruct _md_entry noattr))) ::
               (_lockp, (tptr (Tstruct _atom_int noattr))) ::
               (_t'2, (tptr (Tstruct _md_entry noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _v (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _status tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall (Some _t'1)
          (Evar _get_value (Tfunction ((tptr (Tstruct _node noattr)) :: nil)
                             (tptr tvoid) cc_default))
          ((Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
        (Sset _v (Etempvar _t'1 (tptr tvoid))))
      (Sset _v (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _lookup_md (Tfunction
                             ((tptr (Tstruct _css noattr)) ::
                              (tptr (Tstruct _node noattr)) :: nil)
                             (tptr (Tstruct _md_entry noattr)) cc_default))
          ((Etempvar _c (tptr (Tstruct _css noattr))) ::
           (Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
        (Sset _md (Etempvar _t'2 (tptr (Tstruct _md_entry noattr)))))
      (Ssequence
        (Sset _lockp
          (Efield
            (Ederef (Etempvar _md (tptr (Tstruct _md_entry noattr)))
              (Tstruct _md_entry noattr)) _lock
            (tptr (Tstruct _atom_int noattr))))
        (Ssequence
          (Scall None
            (Evar _release (Tfunction
                             ((tptr (Tstruct _atom_int noattr)) :: nil) tvoid
                             cc_default))
            ((Etempvar _lockp (tptr (Tstruct _atom_int noattr))) :: nil))
          (Sreturn (Some (Etempvar _v (tptr tvoid)))))))))
|}.

Definition f_make_css := {|
  fn_return := (tptr (Tstruct _css noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_new_css, (tptr (Tstruct _css noattr))) :: (_idx, tint) ::
               (_lock, (tptr (Tstruct _atom_int noattr))) ::
               (_t'4, (tptr (Tstruct _atom_int noattr))) ::
               (_t'3, (tptr tvoid)) :: (_t'2, tint) ::
               (_t'1, (tptr tvoid)) ::
               (_t'7, (tptr (Tstruct _md_entry noattr))) ::
               (_t'6, (tptr (Tstruct _md_entry noattr))) ::
               (_t'5, (tptr (Tstruct _md_entry noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _css noattr) tulong) :: nil))
    (Sset _new_css
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _css noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _hash (Tfunction ((tptr tvoid) :: nil) tint cc_default))
        ((Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil))
      (Sset _idx (Etempvar _t'2 tint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _surely_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                 cc_default))
          ((Esizeof (Tstruct _md_entry noattr) tulong) :: nil))
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _new_css (tptr (Tstruct _css noattr)))
                  (Tstruct _css noattr)) _metadata
                (tarray (tptr (Tstruct _md_entry noattr)) 16384))
              (Etempvar _idx tint) (tptr (tptr (Tstruct _md_entry noattr))))
            (tptr (Tstruct _md_entry noattr))) (Etempvar _t'3 (tptr tvoid))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _makelock (Tfunction nil (tptr (Tstruct _atom_int noattr))
                              cc_default)) nil)
          (Sset _lock (Etempvar _t'4 (tptr (Tstruct _atom_int noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _new_css (tptr (Tstruct _css noattr)))
                (Tstruct _css noattr)) _root (tptr (Tstruct _node noattr)))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
          (Ssequence
            (Ssequence
              (Sset _t'7
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _new_css (tptr (Tstruct _css noattr)))
                        (Tstruct _css noattr)) _metadata
                      (tarray (tptr (Tstruct _md_entry noattr)) 16384))
                    (Etempvar _idx tint)
                    (tptr (tptr (Tstruct _md_entry noattr))))
                  (tptr (Tstruct _md_entry noattr))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _t'7 (tptr (Tstruct _md_entry noattr)))
                    (Tstruct _md_entry noattr)) _min tint)
                (Ebinop Osub
                  (Eunop Oneg (Econst_int (Int.repr 2147483647) tint) tint)
                  (Econst_int (Int.repr 1) tint) tint)))
            (Ssequence
              (Ssequence
                (Sset _t'6
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _new_css (tptr (Tstruct _css noattr)))
                          (Tstruct _css noattr)) _metadata
                        (tarray (tptr (Tstruct _md_entry noattr)) 16384))
                      (Etempvar _idx tint)
                      (tptr (tptr (Tstruct _md_entry noattr))))
                    (tptr (Tstruct _md_entry noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _t'6 (tptr (Tstruct _md_entry noattr)))
                      (Tstruct _md_entry noattr)) _max tint)
                  (Econst_int (Int.repr 2147483647) tint)))
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _new_css (tptr (Tstruct _css noattr)))
                            (Tstruct _css noattr)) _metadata
                          (tarray (tptr (Tstruct _md_entry noattr)) 16384))
                        (Etempvar _idx tint)
                        (tptr (tptr (Tstruct _md_entry noattr))))
                      (tptr (Tstruct _md_entry noattr))))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _t'5 (tptr (Tstruct _md_entry noattr)))
                        (Tstruct _md_entry noattr)) _lock
                      (tptr (Tstruct _atom_int noattr)))
                    (Etempvar _lock (tptr (Tstruct _atom_int noattr)))))
                (Ssequence
                  (Scall None
                    (Evar _release (Tfunction
                                     ((tptr (Tstruct _atom_int noattr)) ::
                                      nil) tvoid cc_default))
                    ((Etempvar _lock (tptr (Tstruct _atom_int noattr))) ::
                     nil))
                  (Sreturn (Some (Etempvar _new_css (tptr (Tstruct _css noattr))))))))))))))
|}.

Definition f_get_root := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (Tstruct _css noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_md, (tptr (Tstruct _md_entry noattr))) ::
               (_r, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _md_entry noattr))) ::
               (_t'3, (tptr (Tstruct _atom_int noattr))) ::
               (_t'2, (tptr (Tstruct _atom_int noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _lookup_md (Tfunction
                         ((tptr (Tstruct _css noattr)) ::
                          (tptr (Tstruct _node noattr)) :: nil)
                         (tptr (Tstruct _md_entry noattr)) cc_default))
      ((Etempvar _t (tptr (Tstruct _css noattr))) ::
       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil))
    (Sset _md (Etempvar _t'1 (tptr (Tstruct _md_entry noattr)))))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _md (tptr (Tstruct _md_entry noattr)))
            (Tstruct _md_entry noattr)) _lock
          (tptr (Tstruct _atom_int noattr))))
      (Scall None
        (Evar _acquire (Tfunction ((tptr (Tstruct _atom_int noattr)) :: nil)
                         tvoid cc_default))
        ((Etempvar _t'3 (tptr (Tstruct _atom_int noattr))) :: nil)))
    (Ssequence
      (Sset _r
        (Efield
          (Ederef (Etempvar _t (tptr (Tstruct _css noattr)))
            (Tstruct _css noattr)) _root (tptr (Tstruct _node noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _md (tptr (Tstruct _md_entry noattr)))
                (Tstruct _md_entry noattr)) _lock
              (tptr (Tstruct _atom_int noattr))))
          (Scall None
            (Evar _release (Tfunction
                             ((tptr (Tstruct _atom_int noattr)) :: nil) tvoid
                             cc_default))
            ((Etempvar _t'2 (tptr (Tstruct _atom_int noattr))) :: nil)))
        (Sreturn (Some (Etempvar _r (tptr (Tstruct _node noattr)))))))))
|}.

Definition f_printDS_helper := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (Tstruct _css noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tgt, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _printf (Tfunction ((tptr tschar) :: nil) tint
                    {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
    ((Evar ___stringlit_1 (tarray tschar 19)) :: nil))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_root (Tfunction ((tptr (Tstruct _css noattr)) :: nil)
                          (tptr (Tstruct _node noattr)) cc_default))
        ((Etempvar _t (tptr (Tstruct _css noattr))) :: nil))
      (Sset _tgt (Etempvar _t'1 (tptr (Tstruct _node noattr)))))
    (Scall None
      (Evar _printDS (Tfunction ((tptr (Tstruct _node noattr)) :: nil) tvoid
                       cc_default))
      ((Etempvar _tgt (tptr (Tstruct _node noattr))) :: nil))))
|}.

Definition composites : list composite_definition :=
(Composite _pn Struct
   (Member_plain _p (tptr (Tstruct _node noattr)) ::
    Member_plain _n (tptr (Tstruct _node noattr)) :: nil)
   noattr ::
 Composite _md_entry Struct
   (Member_plain _lock (tptr (Tstruct _atom_int noattr)) ::
    Member_plain _min tint :: Member_plain _max tint :: nil)
   noattr ::
 Composite _css Struct
   (Member_plain _root (tptr (Tstruct _node noattr)) ::
    Member_plain _metadata (tarray (tptr (Tstruct _md_entry noattr)) 16384) ::
    nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) :: (___stringlit_1, Gvar v___stringlit_1) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tint :: nil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tlong :: nil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tlong :: nil) tint cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Xptr :: nil) AST.Xint
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tint
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc, Gfun(External EF_malloc (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_makelock,
   Gfun(External (EF_external "makelock"
                   (mksignature nil AST.Xptr cc_default)) nil
     (tptr (Tstruct _atom_int noattr)) cc_default)) ::
 (_acquire,
   Gfun(External (EF_external "acquire"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _atom_int noattr)) :: nil) tvoid cc_default)) ::
 (_release,
   Gfun(External (EF_external "release"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _atom_int noattr)) :: nil) tvoid cc_default)) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_hash, Gfun(Internal f_hash)) ::
 (_findNext,
   Gfun(External (EF_external "findNext"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xint cc_default))
     ((tptr (Tstruct _node noattr)) ::
      (tptr (tptr (Tstruct _node noattr))) :: tint :: nil) tint cc_default)) ::
 (_insertOp,
   Gfun(External (EF_external "insertOp"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xptr :: nil)
                     AST.Xptr cc_default))
     ((tptr (Tstruct _node noattr)) :: tint :: (tptr tvoid) :: nil)
     (tptr (Tstruct _node noattr)) cc_default)) ::
 (_get_value,
   Gfun(External (EF_external "get_value"
                   (mksignature (AST.Xptr :: nil) AST.Xptr cc_default))
     ((tptr (Tstruct _node noattr)) :: nil) (tptr tvoid) cc_default)) ::
 (_get_key,
   Gfun(External (EF_external "get_key"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr (Tstruct _node noattr)) :: nil) tint cc_default)) ::
 (_printDS,
   Gfun(External (EF_external "printDS"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _node noattr)) :: nil) tvoid cc_default)) ::
 (_inRange, Gfun(Internal f_inRange)) ::
 (_lookup_md, Gfun(Internal f_lookup_md)) ::
 (_traverse, Gfun(Internal f_traverse)) ::
 (_insertOp_helper, Gfun(Internal f_insertOp_helper)) ::
 (_lookupOp_helper, Gfun(Internal f_lookupOp_helper)) ::
 (_make_css, Gfun(Internal f_make_css)) ::
 (_get_root, Gfun(Internal f_get_root)) ::
 (_printDS_helper, Gfun(Internal f_printDS_helper)) :: nil).

Definition public_idents : list ident :=
(_printDS_helper :: _get_root :: _make_css :: _lookupOp_helper ::
 _insertOp_helper :: _traverse :: _lookup_md :: _inRange :: _printDS ::
 _get_key :: _get_value :: _insertOp :: _findNext :: _release :: _acquire ::
 _makelock :: _exit :: _malloc :: _printf :: ___builtin_debug ::
 ___builtin_fmin :: ___builtin_fmax :: ___builtin_fnmsub ::
 ___builtin_fnmadd :: ___builtin_fmsub :: ___builtin_fmadd ::
 ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


