(*
  Differential runner (HOL side) for the hash tier. Run after the
  build:  $HOL/bin/hol < p1_driver.sml
  Three legs, all incremental: BLAKE3 official test vectors, random
  byte-string differentials against fixtures/b3rand-*.bin, and the bind
  layer over every readable fixture (readGeolog, then bindChain, then
  the sealed pipeline). Carries no expectation logic; the run script
  owns comparison.
*)
load "geolog_bindTheory";
load "wordsLib";
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

val dir = "fixtures";

val budget =
  case OS.Process.getEnv "B3_BUDGET" of
    SOME s => (case Int.fromString s of SOME n => n | NONE => 1200)
  | NONE => 1200;

val vec_lens =
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 63, 64, 65, 127, 128, 129, 1023, 1024,
   1025, 2048, 2049, 3072, 3073, 4096, 4097, 5120, 5121, 6144, 6145,
   7168, 7169, 8192, 8193, 16384, 31744, 102400];

fun hexOfBytes tm =
  stringSyntax.fromHOLstring
    (rhs (concl (computeLib.EVAL_CONV
      (mk_comb (prim_mk_const {Name = "hexS", Thy = "geolog_read"}, tm)))));

fun b3hash bs =
  let
    val th = computeLib.EVAL_CONV
               (mk_comb (prim_mk_const {Name = "blake3", Thy = "blake3"},
                         bytesToTerm bs))
  in
    hexOfBytes (rhs (concl th))
  end;

val t_start = Time.now ();
fun elapsed () =
  Time.toReal (Time.- (Time.now (), t_start));

val vec_acc : string list ref = ref [];
fun runVec len =
  if elapsed () > Real.fromInt budget then
    print ("VECTORS-BUDGET-STOP before len=" ^ Int.toString len ^ "\n")
  else
    let
      val input = List.tabulate (len, fn i => i mod 251)
      val t0 = Time.now ()
      val h = b3hash input
      val dt = Time.- (Time.now (), t0)
      val _ = vec_acc := !vec_acc @
                [Int.toString len ^ "\t" ^ h ^ "\n"]
      val _ = writeFile (dir ^ "/b3vectors.hol.txt") (String.concat (!vec_acc))
    in
      print ("VECTOR len=" ^ Int.toString len ^
             " secs=" ^ Time.toString dt ^ "\n")
    end
    handle e =>
      print ("VECTOR len=" ^ Int.toString len ^ " EXCEPTION " ^
             General.exnMessage e ^ "\n");

val _ = List.app runVec vec_lens;

val rand_acc : string list ref = ref [];
fun runRand k =
  let
    val name = "b3rand-" ^ Int.toString k
    val bytes = readBytes (dir ^ "/" ^ name ^ ".bin")
    val h = b3hash bytes
    val _ = rand_acc := !rand_acc @ [name ^ "\t" ^ h ^ "\n"]
    val _ = writeFile (dir ^ "/b3rand.hol.txt") (String.concat (!rand_acc))
  in
    print ("RAND " ^ name ^ " bytes=" ^ Int.toString (length bytes) ^ "\n")
  end
  handle e =>
    print ("RAND b3rand-" ^ Int.toString k ^ " EXCEPTION " ^
           General.exnMessage e ^ "\n");

val _ = List.app runRand [0, 1, 2, 3, 4, 5];

fun renderBind tm =
  stringSyntax.fromHOLstring
    (rhs (concl (computeLib.EVAL_CONV
      (mk_comb (prim_mk_const {Name = "renderBindRes", Thy = "geolog_bind"},
                tm)))));

fun runFixture name =
  let
    val bytes = readBytes (dir ^ "/" ^ name ^ ".geolog")
    val t0 = Time.now ()
    val res_th = computeLib.EVAL_CONV
                   (mk_comb (prim_mk_const {Name = "readGeolog",
                                            Thy = "geolog_read"},
                             bytesToTerm bytes))
    val res = rhs (concl res_th)

    val plain =
      stringSyntax.fromHOLstring
        (rhs (concl (computeLib.EVAL_CONV
          (mk_comb (prim_mk_const {Name = "renderRes", Thy = "geolog_read"},
                    res)))))
    val bind_th = computeLib.EVAL_CONV
                    (Term `case ^res of
                           | ROk g => bindChain g
                           | RErr c t w => BindErr c t w`)
    val bind = rhs (concl bind_th)
    val bindStr = renderBind bind
    val (sealedStr, bindsStr) =
      if constructorName res = "RErr" then (plain, bindStr)
      else
        let
          val cls_th = computeLib.EVAL_CONV
                         (Term `case ^res of
                                | ROk g => sealedCheck g
                                | RErr c t w => NONE`)
          val cls = rhs (concl cls_th)
        in
          if optionSyntax.is_some cls then
            let
              val (t, w) = pairSyntax.dest_pair (optionSyntax.dest_some cls)
              val line =
                "UNSUPPORTED " ^ stringSyntax.fromHOLstring t ^ " " ^
                Arbnum.toString (numSyntax.dest_numeral w) ^ "\n"
            in
              (line, line)
            end
          else if constructorName bind = "BindErr" then (plain, bindStr)
          else
            let
              val b = rand bind
              val sb_th = computeLib.EVAL_CONV
                            (Term `case ^res of
                                   | ROk g => sealedBindCheck g ^b
                                   | RErr c t w => NONE`)
              val sb = rhs (concl sb_th)
            in
              if optionSyntax.is_none sb then (plain, bindStr)
              else
                let
                  val (t, w) =
                    pairSyntax.dest_pair (optionSyntax.dest_some sb)
                in
                  (plain,
                   "UNSUPPORTED " ^ stringSyntax.fromHOLstring t ^ " " ^
                   Arbnum.toString (numSyntax.dest_numeral w) ^ "\n")
                end
            end
        end
    val dt = Time.- (Time.now (), t0)
    val _ = writeFile (dir ^ "/" ^ name ^ ".hol.txt") plain
    val _ = writeFile (dir ^ "/" ^ name ^ ".hols.txt") sealedStr
    val _ = writeFile (dir ^ "/" ^ name ^ ".bind.txt") bindStr
    val _ = writeFile (dir ^ "/" ^ name ^ ".binds.txt") bindsStr
  in
    print ("FIXTURE " ^ name ^ " bytes=" ^ Int.toString (length bytes) ^
           " secs=" ^ Time.toString dt ^ "\n")
  end
  handle e =>
    print ("FIXTURE " ^ name ^ " EXCEPTION " ^ General.exnMessage e ^ "\n");

fun fixtureNames d =
  let
    val ds = OS.FileSys.openDir d
    fun loop acc =
      case OS.FileSys.readDir ds of
        NONE => (OS.FileSys.closeDir ds; acc)
      | SOME f =>
          if String.isSuffix ".geolog" f
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

val names = List.filter (fn n => n <> "chain-all") (fixtureNames dir);
val _ = print ("running " ^ Int.toString (length names) ^ " fixtures\n");
val _ = List.app runFixture names;
val _ = print "P1-DRIVER-DONE\n";

end;
