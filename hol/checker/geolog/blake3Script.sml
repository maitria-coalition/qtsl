(*
  BLAKE3 in HOL: the plain 32-byte hash of a byte string (bytes as
  num list, each < 256), transcribed from the BLAKE3 reference
  implementation — the 8-word IV, 7-round compression with the message
  permutation, chunk/parent tree construction and root output. No keyed
  or derive-key modes, no XOF beyond the first 32 bytes: exactly the
  hash the geolog container's commit identity layer uses. Validated
  against the official test vectors by the accompanying differential
  drivers.
*)
Theory blake3

Ancestors
  arithmetic list rich_list pair words

Definition b3le_def:
  b3le ([]:num list) = (0:num) /\
  b3le (b::bs) = b + 256 * b3le bs
End

Definition w32b_def:
  w32b (w:word32) : num list =
    let v = w2n w in
      [v MOD 256; (v DIV 256) MOD 256; (v DIV 65536) MOD 256;
       (v DIV 16777216) MOD 256]
End

Definition b3w_def:
  b3w (bs:num list) (i:num) : word32 =
    n2w (b3le (TAKE 4 (DROP (4 * i) bs)))
End

Definition b3Words_def:
  b3Words (bs:num list) =
    let p = bs ++ REPLICATE (64 - LENGTH bs) 0 in
      (b3w p 0, b3w p 1, b3w p 2, b3w p 3,
       b3w p 4, b3w p 5, b3w p 6, b3w p 7,
       b3w p 8, b3w p 9, b3w p 10, b3w p 11,
       b3w p 12, b3w p 13, b3w p 14, b3w p 15)
End

Definition b3IVt_def:
  b3IVt = (n2w 0x6A09E667 : word32, n2w 0xBB67AE85 : word32,
           n2w 0x3C6EF372 : word32, n2w 0xA54FF53A : word32,
           n2w 0x510E527F : word32, n2w 0x9B05688C : word32,
           n2w 0x1F83D9AB : word32, n2w 0x5BE0CD19 : word32)
End

Definition b3G_def:
  b3G ((a:word32), (b:word32), (c:word32), (d:word32))
      (mx:word32) (my:word32) =
    let a = a + b + mx in
    let d = (d ?? a) #>> 16 in
    let c = c + d in
    let b = (b ?? c) #>> 12 in
    let a = a + b + my in
    let d = (d ?? a) #>> 8 in
    let c = c + d in
    let b = (b ?? c) #>> 7 in
      (a, b, c, d)
End

Definition b3Round_def:
  b3Round (s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15)
          (m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15) =
    let (s0,s4,s8,s12) = b3G (s0,s4,s8,s12) m0 m1 in
    let (s1,s5,s9,s13) = b3G (s1,s5,s9,s13) m2 m3 in
    let (s2,s6,s10,s14) = b3G (s2,s6,s10,s14) m4 m5 in
    let (s3,s7,s11,s15) = b3G (s3,s7,s11,s15) m6 m7 in
    let (s0,s5,s10,s15) = b3G (s0,s5,s10,s15) m8 m9 in
    let (s1,s6,s11,s12) = b3G (s1,s6,s11,s12) m10 m11 in
    let (s2,s7,s8,s13) = b3G (s2,s7,s8,s13) m12 m13 in
    let (s3,s4,s9,s14) = b3G (s3,s4,s9,s14) m14 m15 in
      (s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15)
End

Definition b3Perm_def:
  b3Perm (m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15) =
    (m2,m6,m3,m10,m7,m0,m4,m13,m1,m11,m12,m5,m9,m14,m15,m8)
End

Definition b3CompressFull_def:
  b3CompressFull ((h0:word32),h1,h2,h3,h4,h5,h6,h7) m
                 (ctr:num) (blen:num) (flags:num) =
    let st = (h0,h1,h2,h3,h4,h5,h6,h7,
              n2w 0x6A09E667 : word32, n2w 0xBB67AE85 : word32,
              n2w 0x3C6EF372 : word32, n2w 0xA54FF53A : word32,
              n2w ctr : word32, n2w (ctr DIV 4294967296) : word32,
              n2w blen : word32, n2w flags : word32) in
    let st = b3Round st m in let m = b3Perm m in
    let st = b3Round st m in let m = b3Perm m in
    let st = b3Round st m in let m = b3Perm m in
    let st = b3Round st m in let m = b3Perm m in
    let st = b3Round st m in let m = b3Perm m in
    let st = b3Round st m in let m = b3Perm m in
    let st = b3Round st m in
    let (v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15) = st in
      (v0 ?? v8, v1 ?? v9, v2 ?? v10, v3 ?? v11,
       v4 ?? v12, v5 ?? v13, v6 ?? v14, v7 ?? v15,
       v8 ?? h0, v9 ?? h1, v10 ?? h2, v11 ?? h3,
       v12 ?? h4, v13 ?? h5, v14 ?? h6, v15 ?? h7)
End

Definition b3CV_def:
  b3CV (v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15) =
    (v0,v1,v2,v3,v4,v5,v6,v7)
End

Definition cat16_def:
  cat16 (a0,a1,a2,a3,a4,a5,a6,a7) (b0,b1,b2,b3,b4,b5,b6,b7) =
    (a0,a1,a2,a3,a4,a5,a6,a7,b0,b1,b2,b3,b4,b5,b6,b7)
End

Definition splitEveryF_def:
  splitEveryF (fuel:num) (n:num) (bs:num list) : (num list) list =
    case fuel of
    | 0 => []
    | SUC f => if n = 0 \/ bs = [] then []
               else TAKE n bs :: splitEveryF f n (DROP n bs)
End

Definition chunksOf_def:
  chunksOf (bs:num list) : (num list) list =
    if bs = [] then [[]] else splitEveryF (LENGTH bs) 1024 bs
End

Definition blocksOfChunk_def:
  blocksOfChunk (bs:num list) : (num list) list =
    if bs = [] then [[]] else splitEveryF (LENGTH bs) 64 bs
End

Definition p2ltF_def:
  p2ltF (fuel:num) (n:num) : num =
    case fuel of
    | 0 => 1
    | SUC f => if n <= 2 then 1 else 2 * p2ltF f ((n + 1) DIV 2)
End

Definition p2lt_def:
  p2lt (n:num) : num = p2ltF n n
End

Datatype:
  b3out = <|
    ocv    : word32 # word32 # word32 # word32 #
             word32 # word32 # word32 # word32 ;
    oblk   : word32 # word32 # word32 # word32 #
             word32 # word32 # word32 # word32 #
             word32 # word32 # word32 # word32 #
             word32 # word32 # word32 # word32 ;
    octr   : num ;
    oblen  : num ;
    oflags : num
  |>
End

Definition b3ChunkA_def:
  b3ChunkA cv (blocks:(num list) list) (ctr:num) (first:bool) : b3out =
    case blocks of
    | [] => <| ocv := cv ; oblk := b3Words [] ; octr := ctr ;
               oblen := 0 ; oflags := (if first then 1 else 0) + 2 |>
    | [b] => <| ocv := cv ; oblk := b3Words b ; octr := ctr ;
                oblen := LENGTH b ;
                oflags := (if first then 1 else 0) + 2 |>
    | (b::rest) =>
        b3ChunkA
          (b3CV (b3CompressFull cv (b3Words b) ctr 64
                                (if first then 1 else 0)))
          rest ctr F
End

Definition b3Chunk_def:
  b3Chunk (ctr:num) (chunk:num list) : b3out =
    b3ChunkA b3IVt (blocksOfChunk chunk) ctr T
End

Definition b3OutCV_def:
  b3OutCV (x:b3out) =
    b3CV (b3CompressFull x.ocv x.oblk x.octr x.oblen x.oflags)
End

Definition b3TreeF_def:
  b3TreeF (fuel:num) (chunks:(num # num list) list) : b3out =
    case fuel of
    | 0 => b3Chunk 0 []
    | SUC f =>
      (case chunks of
       | [] => b3Chunk 0 []
       | [(c, bs)] => b3Chunk c bs
       | _ =>
           let l = p2lt (LENGTH chunks) in
           let lo = b3TreeF f (TAKE l chunks) in
           let ro = b3TreeF f (DROP l chunks) in
             <| ocv := b3IVt ;
                oblk := cat16 (b3OutCV lo) (b3OutCV ro) ;
                octr := 0 ; oblen := 64 ; oflags := 4 |>)
End

Definition b3Tree_def:
  b3Tree (chunks:(num # num list) list) : b3out =
    b3TreeF (LENGTH chunks) chunks
End

Definition b3RootBytes_def:
  b3RootBytes (x:b3out) : num list =
    let (v0,v1,v2,v3,v4,v5,v6,v7) =
        b3CV (b3CompressFull x.ocv x.oblk 0 x.oblen (x.oflags + 8)) in
      w32b v0 ++ w32b v1 ++ w32b v2 ++ w32b v3 ++
      w32b v4 ++ w32b v5 ++ w32b v6 ++ w32b v7
End

Definition blake3_def:
  blake3 (bs:num list) : num list =
    let cs = chunksOf bs in
      b3RootBytes (b3Tree (ZIP (COUNT_LIST (LENGTH cs), cs)))
End
