From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.5"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "fac6.c"%string.
  Definition normalized := true.
End Info.

Definition bool2posdigit (b: bool) : positive -> positive :=
 if b then xI else xO.

Definition string2ident_base : positive := 512.
(* This function converts an Ascii string representing a C identifier
  into a positive number >= string2ident_base.   Characters that more
  frequently appear in C identifiers have shorter encodings. *)
Fixpoint string2ident (s: string) : ident :=
 match s with
 | EmptyString => 512%positive
 | String (Ascii.Ascii b0 b1 b2 b3 b4 b5 b6 b7) r =>
    let r' := string2ident r in
    if (b7 ||
      negb b6 && negb b5 ||
      negb b6 && b5 && negb b4 ||
      b6 && negb b5 && b4 && b3 && negb b2 ||
      b6 && b5 && negb (b4 || b3 || b2 || b1 || b0) ||
      b6 && b5 && b3 && b2)%bool
    then (*these characters should not appear in idents *)
           xI (xI (xI (bool2posdigit b6 (bool2posdigit b5
              (bool2posdigit b4 (bool2posdigit b3
               (bool2posdigit b2 (bool2posdigit b1 
                (bool2posdigit b0 r')))))))))
    else if b6  
    then (* letters, etc. *)
        if b5
        then (* lowercase letters, etc. *)
           xO (bool2posdigit b4 (bool2posdigit b3
               (bool2posdigit b2 (bool2posdigit b1 
                (bool2posdigit b0 r')))))
        else (* uppercase letters, etc. *)
           if (b4 && b3 && b2 && b1 && b0)%bool
           then (* underscore *)
                  xO (xI (xI (xI r')))
           else
           xI (xO (bool2posdigit b4 (bool2posdigit b3
               (bool2posdigit b2 (bool2posdigit b1 
                (bool2posdigit b0 r'))))))
     else (* numbers, etc. *)
          xI (xI (xO (bool2posdigit b4 (bool2posdigit b3
               (bool2posdigit b2 (bool2posdigit b1 
                (bool2posdigit b0 r')))))))
 end.

Ltac string2ident s :=
  let s' := constr:(string2ident s) in
  let s' := eval compute in s' in
  exact s'.

Definition _L : ident := 3%positive.
Definition __191 : ident := ltac:(string2ident "_191"%string).
Definition __192 : ident := ltac:(string2ident "_192"%string).
Definition __252 : ident := ltac:(string2ident "_252"%string).
Definition __253 : ident := ltac:(string2ident "_253"%string).
Definition __254 : ident := ltac:(string2ident "_254"%string).
Definition __Bigint : ident := ltac:(string2ident "_Bigint"%string).
Definition ___builtin_annot : ident := ltac:(string2ident "__builtin_annot"%string).
Definition ___builtin_annot_intval : ident := ltac:(string2ident "__builtin_annot_intval"%string).
Definition ___builtin_bswap : ident := ltac:(string2ident "__builtin_bswap"%string).
Definition ___builtin_bswap16 : ident := ltac:(string2ident "__builtin_bswap16"%string).
Definition ___builtin_bswap32 : ident := ltac:(string2ident "__builtin_bswap32"%string).
Definition ___builtin_bswap64 : ident := ltac:(string2ident "__builtin_bswap64"%string).
Definition ___builtin_clz : ident := ltac:(string2ident "__builtin_clz"%string).
Definition ___builtin_clzl : ident := ltac:(string2ident "__builtin_clzl"%string).
Definition ___builtin_clzll : ident := ltac:(string2ident "__builtin_clzll"%string).
Definition ___builtin_ctz : ident := ltac:(string2ident "__builtin_ctz"%string).
Definition ___builtin_ctzl : ident := ltac:(string2ident "__builtin_ctzl"%string).
Definition ___builtin_ctzll : ident := ltac:(string2ident "__builtin_ctzll"%string).
Definition ___builtin_debug : ident := ltac:(string2ident "__builtin_debug"%string).
Definition ___builtin_fabs : ident := ltac:(string2ident "__builtin_fabs"%string).
Definition ___builtin_fmadd : ident := ltac:(string2ident "__builtin_fmadd"%string).
Definition ___builtin_fmax : ident := ltac:(string2ident "__builtin_fmax"%string).
Definition ___builtin_fmin : ident := ltac:(string2ident "__builtin_fmin"%string).
Definition ___builtin_fmsub : ident := ltac:(string2ident "__builtin_fmsub"%string).
Definition ___builtin_fnmadd : ident := ltac:(string2ident "__builtin_fnmadd"%string).
Definition ___builtin_fnmsub : ident := ltac:(string2ident "__builtin_fnmsub"%string).
Definition ___builtin_fsqrt : ident := ltac:(string2ident "__builtin_fsqrt"%string).
Definition ___builtin_membar : ident := ltac:(string2ident "__builtin_membar"%string).
Definition ___builtin_memcpy_aligned : ident := ltac:(string2ident "__builtin_memcpy_aligned"%string).
Definition ___builtin_nop : ident := ltac:(string2ident "__builtin_nop"%string).
Definition ___builtin_read16_reversed : ident := ltac:(string2ident "__builtin_read16_reversed"%string).
Definition ___builtin_read32_reversed : ident := ltac:(string2ident "__builtin_read32_reversed"%string).
Definition ___builtin_va_arg : ident := ltac:(string2ident "__builtin_va_arg"%string).
Definition ___builtin_va_copy : ident := ltac:(string2ident "__builtin_va_copy"%string).
Definition ___builtin_va_end : ident := ltac:(string2ident "__builtin_va_end"%string).
Definition ___builtin_va_start : ident := ltac:(string2ident "__builtin_va_start"%string).
Definition ___builtin_write16_reversed : ident := ltac:(string2ident "__builtin_write16_reversed"%string).
Definition ___builtin_write32_reversed : ident := ltac:(string2ident "__builtin_write32_reversed"%string).
Definition ___cleanup : ident := 4%positive.
Definition ___compcert_i64_dtos : ident := ltac:(string2ident "__compcert_i64_dtos"%string).
Definition ___compcert_i64_dtou : ident := ltac:(string2ident "__compcert_i64_dtou"%string).
Definition ___compcert_i64_sar : ident := ltac:(string2ident "__compcert_i64_sar"%string).
Definition ___compcert_i64_sdiv : ident := ltac:(string2ident "__compcert_i64_sdiv"%string).
Definition ___compcert_i64_shl : ident := ltac:(string2ident "__compcert_i64_shl"%string).
Definition ___compcert_i64_shr : ident := ltac:(string2ident "__compcert_i64_shr"%string).
Definition ___compcert_i64_smod : ident := ltac:(string2ident "__compcert_i64_smod"%string).
Definition ___compcert_i64_smulh : ident := ltac:(string2ident "__compcert_i64_smulh"%string).
Definition ___compcert_i64_stod : ident := ltac:(string2ident "__compcert_i64_stod"%string).
Definition ___compcert_i64_stof : ident := ltac:(string2ident "__compcert_i64_stof"%string).
Definition ___compcert_i64_udiv : ident := ltac:(string2ident "__compcert_i64_udiv"%string).
Definition ___compcert_i64_umod : ident := ltac:(string2ident "__compcert_i64_umod"%string).
Definition ___compcert_i64_umulh : ident := ltac:(string2ident "__compcert_i64_umulh"%string).
Definition ___compcert_i64_utod : ident := ltac:(string2ident "__compcert_i64_utod"%string).
Definition ___compcert_i64_utof : ident := ltac:(string2ident "__compcert_i64_utof"%string).
Definition ___compcert_va_composite : ident := ltac:(string2ident "__compcert_va_composite"%string).
Definition ___compcert_va_float64 : ident := ltac:(string2ident "__compcert_va_float64"%string).
Definition ___compcert_va_int32 : ident := ltac:(string2ident "__compcert_va_int32"%string).
Definition ___compcert_va_int64 : ident := ltac:(string2ident "__compcert_va_int64"%string).
Definition ___count : ident := 5%positive.
Definition ___getreent : ident := ltac:(string2ident "__getreent"%string).
Definition ___locale_t : ident := 6%positive.
Definition ___sFILE64 : ident := ltac:(string2ident "__sFILE64"%string).
Definition ___sbuf : ident := ltac:(string2ident "__sbuf"%string).
Definition ___sdidinit : ident := 7%positive.
Definition ___sf : ident := 8%positive.
Definition ___sglue : ident := 9%positive.
Definition ___stringlit_1 : ident := 10%positive.
Definition ___stringlit_2 : ident := 11%positive.
Definition ___stringlit_3 : ident := 12%positive.
Definition ___tm : ident := ltac:(string2ident "__tm"%string).
Definition ___tm_hour : ident := 13%positive.
Definition ___tm_isdst : ident := 14%positive.
Definition ___tm_mday : ident := 15%positive.
Definition ___tm_min : ident := 16%positive.
Definition ___tm_mon : ident := 17%positive.
Definition ___tm_sec : ident := 18%positive.
Definition ___tm_wday : ident := 19%positive.
Definition ___tm_yday : ident := 20%positive.
Definition ___tm_year : ident := 21%positive.
Definition ___value : ident := 22%positive.
Definition ___wch : ident := 23%positive.
Definition ___wchb : ident := 24%positive.
Definition __add : ident := 25%positive.
Definition __asctime_buf : ident := 26%positive.
Definition __atexit : ident := ltac:(string2ident "_atexit"%string).
Definition __atexit0 : ident := 27%positive.
Definition __base : ident := 28%positive.
Definition __bf : ident := 29%positive.
Definition __blksize : ident := 30%positive.
Definition __close : ident := 31%positive.
Definition __cookie : ident := 32%positive.
Definition __cvtbuf : ident := 33%positive.
Definition __cvtlen : ident := 34%positive.
Definition __data : ident := 35%positive.
Definition __dso_handle : ident := 36%positive.
Definition __emergency : ident := 37%positive.
Definition __errno : ident := 38%positive.
Definition __file : ident := 39%positive.
Definition __flags : ident := 40%positive.
Definition __flags2 : ident := 41%positive.
Definition __fnargs : ident := 42%positive.
Definition __fns : ident := 43%positive.
Definition __fntypes : ident := 44%positive.
Definition __freelist : ident := 45%positive.
Definition __gamma_signgam : ident := 46%positive.
Definition __getdate_err : ident := 47%positive.
Definition __glue : ident := ltac:(string2ident "_glue"%string).
Definition __h_errno : ident := 48%positive.
Definition __inc : ident := 49%positive.
Definition __ind : ident := 50%positive.
Definition __iobs : ident := 51%positive.
Definition __is_cxa : ident := 52%positive.
Definition __k : ident := 53%positive.
Definition __l64a_buf : ident := 54%positive.
Definition __lb : ident := 55%positive.
Definition __lbfsize : ident := 56%positive.
Definition __locale : ident := 57%positive.
Definition __localtime_buf : ident := 58%positive.
Definition __lock : ident := 59%positive.
Definition __maxwds : ident := 60%positive.
Definition __mblen_state : ident := 61%positive.
Definition __mbrlen_state : ident := 62%positive.
Definition __mbrtowc_state : ident := 63%positive.
Definition __mbsrtowcs_state : ident := 64%positive.
Definition __mbstate : ident := 65%positive.
Definition __mbtowc_state : ident := 66%positive.
Definition __mult : ident := 67%positive.
Definition __nbuf : ident := 68%positive.
Definition __new : ident := 69%positive.
Definition __next : ident := 70%positive.
Definition __nextf : ident := 71%positive.
Definition __niobs : ident := 72%positive.
Definition __nmalloc : ident := 73%positive.
Definition __offset : ident := 74%positive.
Definition __on_exit_args : ident := ltac:(string2ident "_on_exit_args"%string).
Definition __p : ident := 75%positive.
Definition __p5s : ident := 76%positive.
Definition __r : ident := 77%positive.
Definition __r48 : ident := 78%positive.
Definition __rand48 : ident := ltac:(string2ident "_rand48"%string).
Definition __rand_next : ident := 79%positive.
Definition __read : ident := 80%positive.
Definition __reent : ident := ltac:(string2ident "_reent"%string).
Definition __result : ident := 81%positive.
Definition __result_k : ident := 82%positive.
Definition __seed : ident := 83%positive.
Definition __seek : ident := 84%positive.
Definition __seek64 : ident := 85%positive.
Definition __sig_func : ident := 86%positive.
Definition __sign : ident := 87%positive.
Definition __signal_buf : ident := 88%positive.
Definition __size : ident := 89%positive.
Definition __stderr : ident := 90%positive.
Definition __stdin : ident := 91%positive.
Definition __stdout : ident := 92%positive.
Definition __strtok_last : ident := 93%positive.
Definition __ub : ident := 94%positive.
Definition __ubuf : ident := 95%positive.
Definition __unspecified_locale_info : ident := 96%positive.
Definition __unused : ident := 97%positive.
Definition __unused_rand : ident := 98%positive.
Definition __up : ident := 99%positive.
Definition __ur : ident := 100%positive.
Definition __w : ident := 101%positive.
Definition __wcrtomb_state : ident := 102%positive.
Definition __wcsrtombs_state : ident := 103%positive.
Definition __wctomb_state : ident := 104%positive.
Definition __wds : ident := 105%positive.
Definition __write : ident := 106%positive.
Definition __x : ident := 107%positive.
Definition _a : ident := 108%positive.
Definition _argc : ident := 109%positive.
Definition _argv : ident := 110%positive.
Definition _atoi : ident := ltac:(string2ident "atoi"%string).
Definition _b : ident := 111%positive.
Definition _c : ident := 112%positive.
Definition _calc_fac : ident := ltac:(string2ident "calc_fac"%string).
Definition _d : ident := 113%positive.
Definition _exit : ident := ltac:(string2ident "exit"%string).
Definition _fprintf : ident := ltac:(string2ident "fprintf"%string).
Definition _h : ident := ltac:(string2ident "h"%string).
Definition _i : ident := 114%positive.
Definition _l : ident := 115%positive.
Definition _m : ident := 116%positive.
Definition _main : ident := ltac:(string2ident "main"%string).
Definition _malloc : ident := ltac:(string2ident "malloc"%string).
Definition _n : ident := 117%positive.
Definition _print_digits : ident := ltac:(string2ident "print_digits"%string).
Definition _putchar : ident := ltac:(string2ident "putchar"%string).
Definition _t'1 : ident := 118%positive.
Definition _t'10 : ident := 127%positive.
Definition _t'11 : ident := 128%positive.
Definition _t'12 : ident := 129%positive.
Definition _t'13 : ident := 130%positive.
Definition _t'14 : ident := 131%positive.
Definition _t'2 : ident := 119%positive.
Definition _t'3 : ident := 120%positive.
Definition _t'4 : ident := 121%positive.
Definition _t'5 : ident := 122%positive.
Definition _t'6 : ident := 123%positive.
Definition _t'7 : ident := 124%positive.
Definition _t'8 : ident := 125%positive.
Definition _t'9 : ident := 126%positive.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 17);
  gvar_init := (Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 23);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 118) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_h := {|
  gvar_info := tint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_calc_fac := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tuint)) :: (_L, tint) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tulong) :: (_c, tulong) :: (_i, tint) :: (_l, tint) ::
               (_t'1, tint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Etempvar _a (tptr tuint)) (Econst_int (Int.repr 0) tint)
        (tptr tuint)) tuint) (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 1) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _L tint)
                         tint)
            Sskip
            Sbreak)
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tint)
                (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sset _l (Econst_int (Int.repr 1) tint))
      (Ssequence
        (Swhile
          (Etempvar _n tulong)
          (Ssequence
            (Sset _c (Ecast (Econst_int (Int.repr 0) tint) tulong))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                     (Etempvar _l tint) tint)
                        (Sset _t'1 (Econst_int (Int.repr 1) tint))
                        (Sset _t'1 (Ecast (Etempvar _c tulong) tbool)))
                      (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
                    (Ssequence
                      (Ssequence
                        (Sset _t'2
                          (Ederef
                            (Ebinop Oadd (Etempvar _a (tptr tuint))
                              (Etempvar _i tint) (tptr tuint)) tuint))
                        (Sset _b
                          (Ebinop Oadd
                            (Ebinop Omul (Etempvar _n tulong)
                              (Etempvar _t'2 tuint) tulong)
                            (Etempvar _c tulong) tulong)))
                      (Ssequence
                        (Sset _c
                          (Ebinop Odiv (Etempvar _b tulong)
                            (Econst_int (Int.repr 1000000000) tint) tulong))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _a (tptr tuint))
                              (Etempvar _i tint) (tptr tuint)) tuint)
                          (Ebinop Osub (Etempvar _b tulong)
                            (Ebinop Omul (Etempvar _c tulong)
                              (Econst_int (Int.repr 1000000000) tint) tulong)
                            tulong)))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Sifthenelse (Ebinop Ogt (Etempvar _i tint)
                               (Etempvar _l tint) tint)
                  (Sset _l (Etempvar _i tint))
                  Sskip)
                (Sset _n
                  (Ebinop Osub (Etempvar _n tulong)
                    (Econst_int (Int.repr 1) tint) tulong))))))
        (Sreturn (Some (Etempvar _l tint)))))))
|}.

Definition f_print_digits := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_n, tint) :: (_c, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_d, tint) :: (_t'1, tint) :: (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _c tint) (Econst_int (Int.repr 0) tint)
                 tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Scall None
      (Evar _print_digits (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid
                            cc_default))
      ((Ebinop Odiv (Etempvar _n tint) (Econst_int (Int.repr 10) tint) tint) ::
       (Ebinop Osub (Etempvar _c tint) (Econst_int (Int.repr 1) tint) tint) ::
       nil))
    (Ssequence
      (Sset _d
        (Ebinop Omod (Etempvar _n tint) (Econst_int (Int.repr 10) tint) tint))
      (Ssequence
        (Ssequence
          (Sset _t'2 (Evar _h tint))
          (Sifthenelse (Etempvar _t'2 tint)
            (Sset _t'1 (Econst_int (Int.repr 1) tint))
            (Sset _t'1 (Ecast (Etempvar _d tint) tbool))))
        (Sifthenelse (Etempvar _t'1 tint)
          (Ssequence
            (Scall None
              (Evar _putchar (Tfunction (Tcons tint Tnil) tint cc_default))
              ((Ebinop Oadd (Econst_int (Int.repr 48) tint)
                 (Etempvar _d tint) tint) :: nil))
            (Sassign (Evar _h tint) (Econst_int (Int.repr 1) tint)))
          Sskip)))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_argc, tint) :: (_argv, (tptr (tptr tschar))) :: nil);
  fn_vars := nil;
  fn_temps := ((_a, (tptr tuint)) :: (_n, tint) :: (_m, tint) ::
               (_L, tint) :: (_i, tint) :: (_t'6, tint) ::
               (_t'5, (tptr (Tstruct __reent noattr))) ::
               (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr (Tstruct __reent noattr))) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct __reent noattr))) ::
               (_t'14, (tptr tschar)) ::
               (_t'13, (tptr (Tstruct ___sFILE64 noattr))) ::
               (_t'12, (tptr tschar)) :: (_t'11, (tptr tschar)) ::
               (_t'10, (tptr (Tstruct ___sFILE64 noattr))) ::
               (_t'9, (tptr tschar)) ::
               (_t'8, (tptr (Tstruct ___sFILE64 noattr))) :: (_t'7, tuint) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _argc tint)
                   (Econst_int (Int.repr 2) tint) tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar ___getreent (Tfunction Tnil (tptr (Tstruct __reent noattr))
                                cc_default)) nil)
          (Ssequence
            (Sset _t'13
              (Efield
                (Ederef (Etempvar _t'1 (tptr (Tstruct __reent noattr)))
                  (Tstruct __reent noattr)) __stderr
                (tptr (Tstruct ___sFILE64 noattr))))
            (Ssequence
              (Sset _t'14
                (Ederef (Etempvar _argv (tptr (tptr tschar))) (tptr tschar)))
              (Scall None
                (Evar _fprintf (Tfunction
                                 (Tcons (tptr (Tstruct ___sFILE64 noattr))
                                   (Tcons (tptr tschar) Tnil)) tint
                                 {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                ((Etempvar _t'13 (tptr (Tstruct ___sFILE64 noattr))) ::
                 (Evar ___stringlit_1 (tarray tschar 17)) ::
                 (Etempvar _t'14 (tptr tschar)) :: nil)))))
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 2) tint) :: nil)))
      Sskip)
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'12
            (Ederef
              (Ebinop Oadd (Etempvar _argv (tptr (tptr tschar)))
                (Econst_int (Int.repr 1) tint) (tptr (tptr tschar)))
              (tptr tschar)))
          (Scall (Some _t'2)
            (Evar _atoi (Tfunction (Tcons (tptr tschar) Tnil) tint
                          cc_default))
            ((Etempvar _t'12 (tptr tschar)) :: nil)))
        (Sset _n (Etempvar _t'2 tint)))
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _n tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar ___getreent (Tfunction Tnil
                                    (tptr (Tstruct __reent noattr))
                                    cc_default)) nil)
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef (Etempvar _t'3 (tptr (Tstruct __reent noattr)))
                      (Tstruct __reent noattr)) __stderr
                    (tptr (Tstruct ___sFILE64 noattr))))
                (Ssequence
                  (Sset _t'11
                    (Ederef (Etempvar _argv (tptr (tptr tschar)))
                      (tptr tschar)))
                  (Scall None
                    (Evar _fprintf (Tfunction
                                     (Tcons
                                       (tptr (Tstruct ___sFILE64 noattr))
                                       (Tcons (tptr tschar) Tnil)) tint
                                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                    ((Etempvar _t'10 (tptr (Tstruct ___sFILE64 noattr))) ::
                     (Evar ___stringlit_2 (tarray tschar 23)) ::
                     (Etempvar _t'11 (tptr tschar)) :: nil)))))
            (Scall None
              (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
              ((Econst_int (Int.repr 2) tint) :: nil)))
          Sskip)
        (Ssequence
          (Sset _L (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Ssequence
              (Sset _m (Etempvar _n tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Etempvar _m tint) Sskip Sbreak)
                  (Sset _L
                    (Ebinop Oadd (Etempvar _L tint)
                      (Econst_int (Int.repr 1) tint) tint)))
                (Sset _m
                  (Ebinop Odiv (Etempvar _m tint)
                    (Econst_int (Int.repr 10) tint) tint))))
            (Ssequence
              (Sset _L
                (Ebinop Oadd
                  (Ebinop Odiv
                    (Ebinop Omul (Etempvar _L tint) (Etempvar _n tint) tint)
                    (Econst_int (Int.repr 9) tint) tint)
                  (Econst_int (Int.repr 1) tint) tint))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                    cc_default))
                    ((Ebinop Omul (Etempvar _L tint) (Esizeof tuint tuint)
                       tuint) :: nil))
                  (Sset _a (Etempvar _t'4 (tptr tvoid))))
                (Ssequence
                  (Sifthenelse (Eunop Onotbool (Etempvar _a (tptr tuint))
                                 tint)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'5)
                          (Evar ___getreent (Tfunction Tnil
                                              (tptr (Tstruct __reent noattr))
                                              cc_default)) nil)
                        (Ssequence
                          (Sset _t'8
                            (Efield
                              (Ederef
                                (Etempvar _t'5 (tptr (Tstruct __reent noattr)))
                                (Tstruct __reent noattr)) __stderr
                              (tptr (Tstruct ___sFILE64 noattr))))
                          (Ssequence
                            (Sset _t'9
                              (Ederef (Etempvar _argv (tptr (tptr tschar)))
                                (tptr tschar)))
                            (Scall None
                              (Evar _fprintf (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct ___sFILE64 noattr))
                                                 (Tcons (tptr tschar) Tnil))
                                               tint
                                               {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                              ((Etempvar _t'8 (tptr (Tstruct ___sFILE64 noattr))) ::
                               (Evar ___stringlit_3 (tarray tschar 19)) ::
                               (Etempvar _t'9 (tptr tschar)) :: nil)))))
                      (Scall None
                        (Evar _exit (Tfunction (Tcons tint Tnil) tvoid
                                      cc_default))
                        ((Econst_int (Int.repr 1) tint) :: nil)))
                    Sskip)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'6)
                        (Evar _calc_fac (Tfunction
                                          (Tcons (tptr tuint)
                                            (Tcons tint (Tcons tulong Tnil)))
                                          tint cc_default))
                        ((Etempvar _a (tptr tuint)) :: (Etempvar _L tint) ::
                         (Etempvar _n tint) :: nil))
                      (Sset _L (Etempvar _t'6 tint)))
                    (Ssequence
                      (Ssequence
                        (Sset _i
                          (Ebinop Osub (Etempvar _L tint)
                            (Econst_int (Int.repr 1) tint) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                                           (Econst_int (Int.repr 0) tint)
                                           tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _t'7
                                (Ederef
                                  (Ebinop Oadd (Etempvar _a (tptr tuint))
                                    (Etempvar _i tint) (tptr tuint)) tuint))
                              (Scall None
                                (Evar _print_digits (Tfunction
                                                      (Tcons tint
                                                        (Tcons tint Tnil))
                                                      tvoid cc_default))
                                ((Etempvar _t'7 tuint) ::
                                 (Econst_int (Int.repr 9) tint) :: nil))))
                          (Sset _i
                            (Ebinop Osub (Etempvar _i tint)
                              (Econst_int (Int.repr 1) tint) tint))))
                      (Ssequence
                        (Scall None
                          (Evar _putchar (Tfunction (Tcons tint Tnil) tint
                                           cc_default))
                          ((Econst_int (Int.repr 10) tint) :: nil))
                        (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite __192 Union
   ((___wch, tuint) :: (___wchb, (tarray tuchar 4)) :: nil)
   noattr ::
 Composite __191 Struct
   ((___count, tint) :: (___value, (Tunion __192 noattr)) :: nil)
   noattr ::
 Composite __Bigint Struct
   ((__next, (tptr (Tstruct __Bigint noattr))) :: (__k, tint) ::
    (__maxwds, tint) :: (__sign, tint) :: (__wds, tint) ::
    (__x, (tarray tuint 1)) :: nil)
   noattr ::
 Composite ___tm Struct
   ((___tm_sec, tint) :: (___tm_min, tint) :: (___tm_hour, tint) ::
    (___tm_mday, tint) :: (___tm_mon, tint) :: (___tm_year, tint) ::
    (___tm_wday, tint) :: (___tm_yday, tint) :: (___tm_isdst, tint) :: nil)
   noattr ::
 Composite __on_exit_args Struct
   ((__fnargs, (tarray (tptr tvoid) 32)) ::
    (__dso_handle, (tarray (tptr tvoid) 32)) :: (__fntypes, tuint) ::
    (__is_cxa, tuint) :: nil)
   noattr ::
 Composite __atexit Struct
   ((__next, (tptr (Tstruct __atexit noattr))) :: (__ind, tint) ::
    (__fns, (tarray (tptr (Tfunction Tnil tvoid cc_default)) 32)) ::
    (__on_exit_args, (Tstruct __on_exit_args noattr)) :: nil)
   noattr ::
 Composite ___sbuf Struct
   ((__base, (tptr tuchar)) :: (__size, tint) :: nil)
   noattr ::
 Composite ___sFILE64 Struct
   ((__p, (tptr tuchar)) :: (__r, tint) :: (__w, tint) ::
    (__flags, tshort) :: (__file, tshort) ::
    (__bf, (Tstruct ___sbuf noattr)) :: (__lbfsize, tint) ::
    (__data, (tptr (Tstruct __reent noattr))) :: (__cookie, (tptr tvoid)) ::
    (__read,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct __reent noattr))
               (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tuint Tnil))))
             tint cc_default))) ::
    (__write,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct __reent noattr))
               (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tuint Tnil))))
             tint cc_default))) ::
    (__seek,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct __reent noattr))
               (Tcons (tptr tvoid) (Tcons tint (Tcons tint Tnil)))) tint
             cc_default))) ::
    (__close,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct __reent noattr))
               (Tcons (tptr tvoid) Tnil)) tint cc_default))) ::
    (__ub, (Tstruct ___sbuf noattr)) :: (__up, (tptr tuchar)) ::
    (__ur, tint) :: (__ubuf, (tarray tuchar 3)) ::
    (__nbuf, (tarray tuchar 1)) :: (__lb, (Tstruct ___sbuf noattr)) ::
    (__blksize, tint) :: (__flags2, tint) :: (__offset, tlong) ::
    (__seek64,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct __reent noattr))
               (Tcons (tptr tvoid) (Tcons tlong (Tcons tint Tnil)))) tlong
             cc_default))) :: (__lock, (tptr tvoid)) ::
    (__mbstate, (Tstruct __191 noattr)) :: nil)
   noattr ::
 Composite __glue Struct
   ((__next, (tptr (Tstruct __glue noattr))) :: (__niobs, tint) ::
    (__iobs, (tptr (Tstruct ___sFILE64 noattr))) :: nil)
   noattr ::
 Composite __rand48 Struct
   ((__seed, (tarray tushort 3)) :: (__mult, (tarray tushort 3)) ::
    (__add, tushort) :: nil)
   noattr ::
 Composite __253 Struct
   ((__unused_rand, tuint) :: (__strtok_last, (tptr tschar)) ::
    (__asctime_buf, (tarray tschar 26)) ::
    (__localtime_buf, (Tstruct ___tm noattr)) :: (__gamma_signgam, tint) ::
    (__rand_next, tulong) :: (__r48, (Tstruct __rand48 noattr)) ::
    (__mblen_state, (Tstruct __191 noattr)) ::
    (__mbtowc_state, (Tstruct __191 noattr)) ::
    (__wctomb_state, (Tstruct __191 noattr)) ::
    (__l64a_buf, (tarray tschar 8)) :: (__signal_buf, (tarray tschar 24)) ::
    (__getdate_err, tint) :: (__mbrlen_state, (Tstruct __191 noattr)) ::
    (__mbrtowc_state, (Tstruct __191 noattr)) ::
    (__mbsrtowcs_state, (Tstruct __191 noattr)) ::
    (__wcrtomb_state, (Tstruct __191 noattr)) ::
    (__wcsrtombs_state, (Tstruct __191 noattr)) :: (__h_errno, tint) :: nil)
   noattr ::
 Composite __254 Struct
   ((__nextf, (tarray (tptr tuchar) 30)) :: (__nmalloc, (tarray tuint 30)) ::
    nil)
   noattr ::
 Composite __252 Union
   ((__reent, (Tstruct __253 noattr)) ::
    (__unused, (Tstruct __254 noattr)) :: nil)
   noattr ::
 Composite __reent Struct
   ((__errno, tint) :: (__stdin, (tptr (Tstruct ___sFILE64 noattr))) ::
    (__stdout, (tptr (Tstruct ___sFILE64 noattr))) ::
    (__stderr, (tptr (Tstruct ___sFILE64 noattr))) :: (__inc, tint) ::
    (__emergency, (tarray tschar 25)) :: (__unspecified_locale_info, tint) ::
    (__locale, (tptr (Tstruct ___locale_t noattr))) :: (___sdidinit, tint) ::
    (___cleanup,
     (tptr (Tfunction (Tcons (tptr (Tstruct __reent noattr)) Tnil) tvoid
             cc_default))) :: (__result, (tptr (Tstruct __Bigint noattr))) ::
    (__result_k, tint) :: (__p5s, (tptr (Tstruct __Bigint noattr))) ::
    (__freelist, (tptr (tptr (Tstruct __Bigint noattr)))) ::
    (__cvtlen, tint) :: (__cvtbuf, (tptr tschar)) ::
    (__new, (Tunion __252 noattr)) ::
    (__atexit, (tptr (Tstruct __atexit noattr))) ::
    (__atexit0, (Tstruct __atexit noattr)) ::
    (__sig_func,
     (tptr (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default)))) ::
    (___sglue, (Tstruct __glue noattr)) ::
    (___sf, (tarray (Tstruct ___sFILE64 noattr) 3)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___getreent,
   Gfun(External (EF_external "__getreent"
                   (mksignature nil (Some AST.Tint) cc_default)) Tnil
     (tptr (Tstruct __reent noattr)) cc_default)) ::
 (_fprintf,
   Gfun(External (EF_external "fprintf"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr (Tstruct ___sFILE64 noattr)) (Tcons (tptr tschar) Tnil))
     tint {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_putchar,
   Gfun(External (EF_external "putchar"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tint Tnil) tint cc_default)) ::
 (_atoi,
   Gfun(External (EF_external "atoi"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tschar) Tnil) tint cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_h, Gvar v_h) :: (_calc_fac, Gfun(Internal f_calc_fac)) ::
 (_print_digits, Gfun(Internal f_print_digits)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _print_digits :: _calc_fac :: _h :: _malloc :: _exit :: _atoi ::
 _putchar :: _fprintf :: ___getreent :: ___builtin_debug :: ___builtin_nop ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fsqrt :: ___builtin_fabs ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


