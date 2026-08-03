(*
  Differential runner (HOL side) for the geolog reader. Run after the
  build, from this directory:  $HOL/bin/hol < diff_driver.sml
  For every fixtures/<name>.geolog it evaluates readGeolog once, renders
  the result to fixtures/<name>.hol.txt, then applies the sealed
  classifier and writes fixtures/<name>.hols.txt. Deliberately carries
  no expectation logic — run-differential.sh owns the comparison, so the
  instrument stays blind to the expected answers.
*)
load "geolog_readTheory";
load "stringSyntax";
load "optionSyntax";
load "pairSyntax";
load "numSyntax";
load "listSyntax";

local
  open HolKernel boolLib bossLib;
in

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

fun constructorName tm = fst (dest_const (fst (strip_comb tm)));

fun runFixture dir name =
  let
    val bytes = readBytes (dir ^ "/" ^ name ^ ".geolog")
    val t0 = Time.now ()
    val res_th = computeLib.EVAL_CONV
                   (mk_comb (prim_mk_const {Name = "readGeolog",
                                            Thy = "geolog_read"},
                             bytesToTerm bytes))
    val res = rhs (concl res_th)
    val plain_th = computeLib.EVAL_CONV
                     (mk_comb (prim_mk_const {Name = "renderRes",
                                              Thy = "geolog_read"}, res))
    val plain = stringSyntax.fromHOLstring (rhs (concl plain_th))
    val sealed =
      if constructorName res = "RErr" then plain
      else
        let
          val cls_th = computeLib.EVAL_CONV
                         (Term `case ^res of
                                | ROk g => sealedCheck g
                                | RErr c t w => NONE`)
          val cls = rhs (concl cls_th)
        in
          if optionSyntax.is_none cls then plain
          else
            let
              val tw = optionSyntax.dest_some cls
              val (t, w) = pairSyntax.dest_pair tw
            in
              "UNSUPPORTED " ^ stringSyntax.fromHOLstring t ^ " " ^
              Arbnum.toString (numSyntax.dest_numeral w) ^ "\n"
            end
        end
    val dt = Time.- (Time.now (), t0)
    val _ = writeFile (dir ^ "/" ^ name ^ ".hol.txt") plain
    val _ = writeFile (dir ^ "/" ^ name ^ ".hols.txt") sealed
  in
    print ("FIXTURE " ^ name ^ " bytes=" ^ Int.toString (length bytes) ^
           " secs=" ^ Time.toString dt ^ "\n")
  end
  handle e =>
    print ("FIXTURE " ^ name ^ " EXCEPTION " ^ General.exnMessage e ^ "\n");

fun fixtureNames dir =
  let
    val ds = OS.FileSys.openDir dir
    fun loop acc =
      case OS.FileSys.readDir ds of
        NONE => (OS.FileSys.closeDir ds; acc)
      | SOME f =>
          if String.isSuffix ".geolog" f
          then loop (String.substring (f, 0, String.size f - 7) :: acc)
          else loop acc
    val names = loop []
    fun size n =
      OS.FileSys.fileSize (dir ^ "/" ^ n ^ ".geolog") handle _ => 0
    val sized = map (fn n => (size n, n)) names
  in

    map #2 (Lib.sort
              (fn (a, x) => fn (b, y) =>
                 a < b orelse (a = b andalso String.<= (x, y)))
              sized)
  end;

val dir = "fixtures";
val names = fixtureNames dir;
val _ = print ("running " ^ Int.toString (length names) ^ " fixtures\n");
val _ = List.app (runFixture dir) names;
val _ = print "DIFF-DRIVER-DONE\n";

end;
