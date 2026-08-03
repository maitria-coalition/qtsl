(*
  Differential runner (HOL side) for the composed certificate
  verdict. Run after the build:  $HOL/bin/hol < p3_driver.sml
  Evaluates the end-to-end checkGeologCert on the cert-* fixtures and
  writes rendered verdicts beside the expected-output oracles. Carries
  no expectation logic; the run script owns comparison.
*)
load "geolog_verdictTheory";
load "geolog_certDemoTheory";
load "wordsLib";
load "stringSyntax";
load "numSyntax";
load "listSyntax";
load "pairSyntax";
load "optionSyntax";

local
  open HolKernel boolLib bossLib;
in

val have_staged =
  (load "geolog_certPinsTheory"; true)
  handle _ => (print "NO-STAGED-PINS (cert-real-* will be skipped)\n";
               false);

fun readBytes path =
  let
    val ins = BinIO.openIn path
    val vec = BinIO.inputAll ins
    val _ = BinIO.closeIn ins
  in
    Word8Vector.foldr (fn (w, acc) => Word8.toInt w :: acc) [] vec
  end;

fun bytesToTerm bs =
  listSyntax.mk_list (map numSyntax.term_of_int bs, numSyntax.num);

fun writeFile path s =
  let val out = TextIO.openOut path
  in TextIO.output (out, s); TextIO.closeOut out end;

val dir = "geolog/fixtures";

val demoPins_tm =
  prim_mk_const {Name = "demoPins", Thy = "geolog_certDemo"};

fun stagedPins_tm () =
  prim_mk_const {Name = "stagedPins", Thy = "geolog_certPins"};

fun pinsFor name =
  if String.isPrefix "cert-real-" name
  then if have_staged then SOME (stagedPins_tm ()) else NONE
  else SOME demoPins_tm;

fun c thy n = prim_mk_const {Name = n, Thy = thy};
val EV = computeLib.EVAL_CONV;
fun ev tm = rhs (concl (EV tm));
fun conName tm = fst (dest_const (fst (strip_comb tm)));

fun expectCon stage cons tm =
  let val h = conName tm handle _ => "<nonconst>"
  in
    if List.exists (fn x => x = h) cons then tm
    else raise Fail ("STUCK-EVAL at " ^ stage ^ ": head " ^ h)
  end;

fun vd_of_class cls t w =
  mk_comb (mk_comb
    (c "geolog_verdict"
       (if cls = "CUnread" then "VdUnreadable" else "VdUnsupported"),
     t), w);

fun verdictOf pins bst =
  let
    val res = expectCon "read" ["RErr", "ROk"]
                (ev (mk_comb (c "geolog_read" "readGeologSealed", bst)))
  in
    if conName res = "RErr" then
      let val (_, [cls, t, w]) = strip_comb res
      in vd_of_class (conName cls) t w end
    else
    let
      val g = rand res
      val bind = expectCon "bind" ["BindErr", "BindOk"]
                   (ev (mk_comb (c "geolog_bind" "bindChain", g)))
    in
      if conName bind = "BindErr" then
        let val (_, [cls, t, w]) = strip_comb bind
        in vd_of_class (conName cls) t w end
      else
      let
        val b = rand bind
        val sealed = expectCon "sealedR" ["NONE", "SOME"]
                       (ev (list_mk_comb
                              (c "geolog_cert" "sealedBindCheckR",
                               [pins, g, b])))
      in
        if optionSyntax.is_some sealed then
          let val (t, w) = pairSyntax.dest_pair
                             (optionSyntax.dest_some sealed)
          in mk_comb (mk_comb (c "geolog_verdict" "VdUnsupported", t), w)
          end
        else
        let
          val cres = expectCon "cert" ["CErr", "COk"]
                       (ev (list_mk_comb
                              (c "geolog_cert" "certOfRows", [pins, g])))
        in
          if conName cres = "CErr" then
            let val (_, [cls, t, w]) = strip_comb cres
            in vd_of_class (conName cls) t w end
          else
          let
            val cols = rand cres
            val joins = expectCon "joins" ["NONE", "SOME"]
                          (ev (mk_comb (c "qtsl_joins" "checkJoins", cols)))
            fun reject tag =
              mk_comb (mk_comb (c "geolog_verdict" "VdReject",
                                stringSyntax.fromMLstring tag),
                       numSyntax.term_of_int 0)
          in
            if optionSyntax.is_none joins then reject "ctx_none"
            else if aconv (optionSyntax.dest_some joins) boolSyntax.F
            then reject "joins"
            else
              let
                val tip = ev (Term `(^b).btip`)
                val stmt = ev (Term `(^cols).hdrImage`)
              in
                mk_comb (mk_comb (c "geolog_verdict" "VdVerified", tip),
                         stmt)
              end
          end
        end
      end
    end
  end;

val renderVerdict_tm = c "geolog_verdict" "renderVerdict";

fun alreadyDone name =
  OS.FileSys.access (dir ^ "/" ^ name ^ ".cert.txt", []);

fun runFixture name =
  if alreadyDone name then print ("RESUME-SKIP " ^ name ^ " (done)\n")
  else
  case pinsFor name of
    NONE => print ("SKIP " ^ name ^ " (no staged pins)\n")
  | SOME pins =>
      let
        val bytes = readBytes (dir ^ "/" ^ name ^ ".geolog")
        val t0 = Time.now ()
        val v = verdictOf pins (bytesToTerm bytes)
        val s = stringSyntax.fromHOLstring
                  (ev (mk_comb (renderVerdict_tm, v)))
        val dt = Time.- (Time.now (), t0)
        val _ = writeFile (dir ^ "/" ^ name ^ ".cert.txt") s
      in
        print ("FIXTURE " ^ name ^ " bytes=" ^ Int.toString (length bytes) ^
               " secs=" ^ Time.toString dt ^ "\n")
      end
      handle e =>
        print ("FIXTURE " ^ name ^ " EXCEPTION " ^
               General.exnMessage e ^ "\n");

fun fixtureNames d =
  let
    val ds = OS.FileSys.openDir d
    fun loop acc =
      case OS.FileSys.readDir ds of
        NONE => (OS.FileSys.closeDir ds; acc)
      | SOME f =>
          if String.isSuffix ".geolog" f andalso String.isPrefix "cert-" f
          then loop (String.substring (f, 0, String.size f - 7) :: acc)
          else loop acc
    val names = loop []
    fun size n =
      OS.FileSys.fileSize (d ^ "/" ^ n ^ ".geolog") handle _ => 0
    val sized = map (fn n => (size n, n)) names
  in
    map #2 (Lib.sort
              (fn (a, x) => fn (b, y) =>
                 a < b orelse (a = b andalso String.<= (x, y)))
              sized)
  end;

val names = fixtureNames dir;
val _ = print ("running " ^ Int.toString (length names) ^
               " cert fixtures\n");
val _ = List.app runFixture names;
val _ = print "P3-DRIVER-DONE\n";

end;
