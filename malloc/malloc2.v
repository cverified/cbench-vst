From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.7"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "malloc2.c"%string.
  Definition normalized := true.
End Info.

Definition _T_alloc : ident := 62%positive.
Definition _T_free : ident := 64%positive.
Definition _T_ptr : ident := 63%positive.
Definition __908 : ident := 2%positive.
Definition ___builtin_annot : ident := 14%positive.
Definition ___builtin_annot_intval : ident := 15%positive.
Definition ___builtin_bswap : ident := 7%positive.
Definition ___builtin_bswap16 : ident := 9%positive.
Definition ___builtin_bswap32 : ident := 8%positive.
Definition ___builtin_bswap64 : ident := 6%positive.
Definition ___builtin_clz : ident := 40%positive.
Definition ___builtin_clzl : ident := 41%positive.
Definition ___builtin_clzll : ident := 42%positive.
Definition ___builtin_ctz : ident := 43%positive.
Definition ___builtin_ctzl : ident := 44%positive.
Definition ___builtin_ctzll : ident := 45%positive.
Definition ___builtin_debug : ident := 56%positive.
Definition ___builtin_fabs : ident := 10%positive.
Definition ___builtin_fmadd : ident := 48%positive.
Definition ___builtin_fmax : ident := 46%positive.
Definition ___builtin_fmin : ident := 47%positive.
Definition ___builtin_fmsub : ident := 49%positive.
Definition ___builtin_fnmadd : ident := 50%positive.
Definition ___builtin_fnmsub : ident := 51%positive.
Definition ___builtin_fsqrt : ident := 11%positive.
Definition ___builtin_membar : ident := 16%positive.
Definition ___builtin_memcpy_aligned : ident := 12%positive.
Definition ___builtin_read16_reversed : ident := 52%positive.
Definition ___builtin_read32_reversed : ident := 53%positive.
Definition ___builtin_sel : ident := 13%positive.
Definition ___builtin_va_arg : ident := 18%positive.
Definition ___builtin_va_copy : ident := 19%positive.
Definition ___builtin_va_end : ident := 20%positive.
Definition ___builtin_va_start : ident := 17%positive.
Definition ___builtin_write16_reversed : ident := 54%positive.
Definition ___builtin_write32_reversed : ident := 55%positive.
Definition ___compcert_i64_dtos : ident := 25%positive.
Definition ___compcert_i64_dtou : ident := 26%positive.
Definition ___compcert_i64_sar : ident := 37%positive.
Definition ___compcert_i64_sdiv : ident := 31%positive.
Definition ___compcert_i64_shl : ident := 35%positive.
Definition ___compcert_i64_shr : ident := 36%positive.
Definition ___compcert_i64_smod : ident := 33%positive.
Definition ___compcert_i64_smulh : ident := 38%positive.
Definition ___compcert_i64_stod : ident := 27%positive.
Definition ___compcert_i64_stof : ident := 29%positive.
Definition ___compcert_i64_udiv : ident := 32%positive.
Definition ___compcert_i64_umod : ident := 34%positive.
Definition ___compcert_i64_umulh : ident := 39%positive.
Definition ___compcert_i64_utod : ident := 28%positive.
Definition ___compcert_i64_utof : ident := 30%positive.
Definition ___compcert_va_composite : ident := 24%positive.
Definition ___compcert_va_float64 : ident := 23%positive.
Definition ___compcert_va_int32 : ident := 21%positive.
Definition ___compcert_va_int64 : ident := 22%positive.
Definition ___stringlit_1 : ident := 69%positive.
Definition ___stringlit_2 : ident := 70%positive.
Definition _allocated : ident := 3%positive.
Definition _cell : ident := 4%positive.
Definition _contents : ident := 1%positive.
Definition _dest : ident := 65%positive.
Definition _first_free : ident := 60%positive.
Definition _heap : ident := 58%positive.
Definition _limit : ident := 59%positive.
Definition _main : ident := 71%positive.
Definition _next_free : ident := 5%positive.
Definition _p : ident := 68%positive.
Definition _printf : ident := 57%positive.
Definition _ptr : ident := 61%positive.
Definition _src : ident := 66%positive.
Definition _vstrcpy : ident := 67%positive.
Definition _t'1 : ident := 72%positive.
Definition _t'2 : ident := 73%positive.
Definition _t'3 : ident := 74%positive.
Definition _t'4 : ident := 75%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_heap := {|
  gvar_info := (tarray (Tunion _cell noattr) 1000);
  gvar_init := (Init_space 44000 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_limit := {|
  gvar_info := (tptr (Tunion _cell noattr));
  gvar_init := (Init_addrof _heap (Ptrofs.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_first_free := {|
  gvar_info := (tptr (Tunion _cell noattr));
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_T_alloc := {|
  fn_return := (tptr (Tstruct __908 noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_ptr, (tptr (Tunion _cell noattr))) ::
               (_t'1, (tptr (Tunion _cell noattr))) ::
               (_t'4, (tptr (Tunion _cell noattr))) ::
               (_t'3, (tptr (Tunion _cell noattr))) ::
               (_t'2, (tptr (Tunion _cell noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _ptr (Evar _first_free (tptr (Tunion _cell noattr))))
  (Ssequence
    (Sifthenelse (Etempvar _ptr (tptr (Tunion _cell noattr)))
      (Ssequence
        (Sset _t'3 (Evar _first_free (tptr (Tunion _cell noattr))))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _t'3 (tptr (Tunion _cell noattr)))
                (Tunion _cell noattr)) _next_free
              (tptr (Tunion _cell noattr))))
          (Sassign (Evar _first_free (tptr (Tunion _cell noattr)))
            (Etempvar _t'4 (tptr (Tunion _cell noattr))))))
      (Ssequence
        (Ssequence
          (Sset _t'2 (Evar _limit (tptr (Tunion _cell noattr))))
          (Sifthenelse (Ebinop Oge
                         (Etempvar _t'2 (tptr (Tunion _cell noattr)))
                         (Ebinop Oadd
                           (Evar _heap (tarray (Tunion _cell noattr) 1000))
                           (Econst_int (Int.repr 1000) tint)
                           (tptr (Tunion _cell noattr))) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip))
        (Ssequence
          (Ssequence
            (Sset _t'1 (Evar _limit (tptr (Tunion _cell noattr))))
            (Sassign (Evar _limit (tptr (Tunion _cell noattr)))
              (Ebinop Oadd (Etempvar _t'1 (tptr (Tunion _cell noattr)))
                (Econst_int (Int.repr 1) tint) (tptr (Tunion _cell noattr)))))
          (Sset _ptr (Etempvar _t'1 (tptr (Tunion _cell noattr)))))))
    (Sreturn (Some (Eaddrof
                     (Efield
                       (Ederef (Etempvar _ptr (tptr (Tunion _cell noattr)))
                         (Tunion _cell noattr)) _allocated
                       (Tstruct __908 noattr)) (tptr (Tstruct __908 noattr)))))))
|}.

Definition f_T_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_T_ptr, (tptr (Tstruct __908 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_ptr, (tptr (Tunion _cell noattr))) ::
               (_t'1, (tptr (Tunion _cell noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _ptr
    (Ecast (Etempvar _T_ptr (tptr (Tstruct __908 noattr)))
      (tptr (Tunion _cell noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'1 (Evar _first_free (tptr (Tunion _cell noattr))))
      (Sassign
        (Efield
          (Ederef (Etempvar _ptr (tptr (Tunion _cell noattr)))
            (Tunion _cell noattr)) _next_free (tptr (Tunion _cell noattr)))
        (Etempvar _t'1 (tptr (Tunion _cell noattr)))))
    (Sassign (Evar _first_free (tptr (Tunion _cell noattr)))
      (Etempvar _ptr (tptr (Tunion _cell noattr))))))
|}.

Definition f_vstrcpy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dest, (tptr tschar)) :: (_src, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tschar)) :: (_t'1, (tptr tschar)) ::
               (_t'4, tschar) :: (_t'3, tschar) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    (Ssequence
      (Sset _t'4 (Ederef (Etempvar _src (tptr tschar)) tschar))
      (Sifthenelse (Etempvar _t'4 tschar) Sskip Sbreak))
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1 (Etempvar _dest (tptr tschar)))
            (Sset _dest
              (Ebinop Oadd (Etempvar _t'1 (tptr tschar))
                (Econst_int (Int.repr 1) tint) (tptr tschar))))
          (Sset _t'2 (Etempvar _src (tptr tschar))))
        (Sset _src
          (Ebinop Oadd (Etempvar _t'2 (tptr tschar))
            (Econst_int (Int.repr 1) tint) (tptr tschar))))
      (Ssequence
        (Sset _t'3 (Ederef (Etempvar _t'2 (tptr tschar)) tschar))
        (Sassign (Ederef (Etempvar _t'1 (tptr tschar)) tschar)
          (Etempvar _t'3 tschar)))))
  Sskip)
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct __908 noattr))) ::
               (_t'1, (tptr (Tstruct __908 noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _T_alloc (Tfunction Tnil (tptr (Tstruct __908 noattr))
                         cc_default)) nil)
      (Sset _p (Etempvar _t'1 (tptr (Tstruct __908 noattr)))))
    (Ssequence
      (Scall None
        (Evar _vstrcpy (Tfunction
                         (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil))
                         tvoid cc_default))
        ((Efield
           (Ederef (Etempvar _p (tptr (Tstruct __908 noattr)))
             (Tstruct __908 noattr)) _contents (tarray tschar 42)) ::
         (Evar ___stringlit_1 (tarray tschar 4)) :: nil))
      (Ssequence
        (Scall None
          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
          ((Evar ___stringlit_2 (tarray tschar 4)) ::
           (Efield
             (Ederef (Etempvar _p (tptr (Tstruct __908 noattr)))
               (Tstruct __908 noattr)) _contents (tarray tschar 42)) :: nil))
        (Ssequence
          (Scall None
            (Evar _T_free (Tfunction
                            (Tcons (tptr (Tstruct __908 noattr)) Tnil) tvoid
                            cc_default))
            ((Etempvar _p (tptr (Tstruct __908 noattr))) :: nil))
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite __908 Struct ((_contents, (tarray tschar 42)) :: nil) noattr ::
 Composite _cell Union
   ((_allocated, (Tstruct __908 noattr)) ::
    (_next_free, (tptr (Tunion _cell noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) AST.Tint
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_heap, Gvar v_heap) :: (_limit, Gvar v_limit) ::
 (_first_free, Gvar v_first_free) :: (_T_alloc, Gfun(Internal f_T_alloc)) ::
 (_T_free, Gfun(Internal f_T_free)) ::
 (_vstrcpy, Gfun(Internal f_vstrcpy)) :: (_main, Gfun(Internal f_main)) ::
 nil).

Definition public_idents : list ident :=
(_main :: _vstrcpy :: _T_free :: _T_alloc :: _first_free :: _limit ::
 _heap :: _printf :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


