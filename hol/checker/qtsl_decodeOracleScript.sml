(*
  Byte-exact oracle runs (UNTRUSTED INSTRUMENT): for each committed
  column dump in oracle-dumps/, builds the columns term, evaluates
  decodeSpec in-logic via cv_compute, and banks one theorem per fixture
  equating the result with the reference decoder's output bytes. A
  diagnostic, never part of the trusted chain; building it requires the
  dumps directory.
*)
open HolKernel Parse boolLib bossLib;
open listTheory pairTheory optionTheory;
open qtsl_decodeSpecTheory cv_transLib;

val _ = new_theory "qtsl_decodeOracle";

val _ = cv_auto_trans decodeSpec_def;

fun read_file path =
  let val ins = TextIO.openIn path
      val s = TextIO.inputAll ins
      val _ = TextIO.closeIn ins
  in s end

val numty = numSyntax.num
val nlist_ty = listSyntax.mk_list_type numty
fun mk_num n = numSyntax.mk_numeral n
fun mk_nlist ls = listSyntax.mk_list (map mk_num ls, numty)
fun mk_nllist ls = listSyntax.mk_list (map mk_nlist ls, nlist_ty)

val columns_con =
  case TypeBase.constructors_of “:columns” of
    [c] => c
  | _ => raise Fail "columns: expected one constructor"

fun parse_dump path =
  let
    val ts = ref (String.tokens Char.isSpace (read_file path))
    fun pop () = case !ts of [] => raise Fail "dump eof" | h::t => (ts := t; h)
    fun popn () = case Arbnum.fromString (pop ()) of n => n
    fun popi () = Arbnum.toInt (popn ())
    fun list0 () = List.tabulate (popi (), fn _ => popn ())
    val _ = (pop () = "BSGCCOLS1") orelse raise Fail "dump magic"
    val hdr = list0 ()
    val topo = popn () val dflt = popn ()
    val nN = popn () val nP = popn () val bS = popn ()
    val ntag = list0 ()
    val nar = list0 ()
    val ntp = list0 ()
    val ncl = list0 ()
    val npf = list0 ()
    val nsc = list0 ()
    val nden = List.tabulate (popi (), fn _ =>
                 let val a = popn () val b = popn () in (a, b) end)
    val npath = List.tabulate (popi (), fn _ =>
                  let val st = list0 () val ifc = list0 () in (st, ifc) end)
    val nrat = list0 ()
    val ne1 = list0 ()
    val ne2 = list0 ()
    val ptag = list0 ()
    val pref = list0 ()
    val pnl = list0 ()
    val pdi = list0 ()
    val pdd = List.tabulate (popi (), fn _ => list0 ())
    val pnum = list0 ()
    val pmisc = list0 ()
    val _ = (pop () = "EXPECT") orelse raise Fail "dump EXPECT"
    val v0 = list0 ()
    val _ = (null (!ts)) orelse raise Fail "dump trailing tokens"
    val nden_tm =
      listSyntax.mk_list
        (map (fn (a, b) => pairSyntax.mk_pair (mk_num a, mk_num b)) nden,
         pairSyntax.mk_prod (numty, numty))
    val npath_tm =
      listSyntax.mk_list
        (map (fn (st, ifc) => pairSyntax.mk_pair (mk_nlist st, mk_nlist ifc)) npath,
         pairSyntax.mk_prod (nlist_ty, nlist_ty))
    val cols_tm =
      list_mk_comb (columns_con,
        [mk_nlist hdr, mk_num topo, mk_num dflt, mk_num nN, mk_num nP,
         mk_num bS, mk_nlist ntag, mk_nlist nar, mk_nlist ntp, mk_nlist ncl,
         mk_nlist npf, mk_nlist nsc, nden_tm, npath_tm, mk_nlist nrat,
         mk_nlist ne1, mk_nlist ne2, mk_nlist ptag, mk_nlist pref,
         mk_nlist pnl, mk_nlist pdi, mk_nllist pdd, mk_nlist pnum,
         mk_nlist pmisc])
  in (cols_tm, v0) end

val fixtures = [
  "cartpole_core_decrease", "cartpole_core_rate",
  "dp_composite_smallgain", "dp_composite_syzygy",
  "ou_avoid_barrier", "ou_avoid_gen", "ou_avoid_nonneg",
  "ou_deadline_q2_barrier", "ou_deadline_q2_gen",
  "ou_deadline_q4_barrier", "ou_deadline_q4_gen",
  "pdmp_jump_decrease",
  "terms_v1_bern_fastpath", "terms_v1_mono_general",
  "terms_v1_multivar_fastpath",
  "thermostat_guard_sep", "thermostat_off_gen", "thermostat_on_gen"
];

val failures : string list ref = ref []

fun run_fixture name =
  let
    val (cols_tm, v0) = parse_dump ("oracle-dumps/" ^ name ^ ".cols")
    val expect_tm = optionSyntax.mk_some (mk_nlist v0)
    val t0 = Time.now ()
    val th = cv_eval (mk_comb (“decodeSpec”, cols_tm))
    val dt = Time.toMilliseconds (Time.- (Time.now (), t0))
    val result = boolSyntax.rhs (concl th)
  in
    if aconv result expect_tm then
      (save_thm ("oracle_" ^ name, th);
       print ("ORACLE OK " ^ name ^ " (" ^ Int.toString (length v0) ^
              " bytes, cv_eval " ^ LargeInt.toString dt ^ " ms)\n"))
    else
      let
        val got =
          if optionSyntax.is_some result then
            map numSyntax.dest_numeral
                (fst (listSyntax.dest_list (optionSyntax.dest_some result)))
          else []
        fun firstdiff (i, x::xs, y::ys) =
              if Arbnum.compare (x, y) = EQUAL then firstdiff (i+1, xs, ys)
              else "first diff at byte " ^ Int.toString i
          | firstdiff (i, [], []) = "no diff?!"
          | firstdiff (i, _, _) = "length diff at " ^ Int.toString i
        val why =
          if null got andalso not (optionSyntax.is_some result)
          then "decodeSpec returned NONE"
          else firstdiff (0, got, v0) ^ " (got " ^ Int.toString (length got) ^
               " bytes, want " ^ Int.toString (length v0) ^ ")"
      in
        (print ("ORACLE MISMATCH " ^ name ^ ": " ^ why ^ "\n");
         failures := name :: !failures)
      end
  end

val _ = List.app run_fixture fixtures

val _ =
  if null (!failures) then print "ORACLE: all 18 fixtures byte-exact\n"
  else raise Fail ("oracle mismatches: " ^ String.concatWith ", " (!failures))

val _ = export_theory ();
