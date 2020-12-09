data Binary bs;
data EQ;
data LT;
data GT;
data ,;
data , a;
data , a b;
data , a b c;
data , a b c d;
data True;
data False;
data Nothing;
data Just x;

False `Not` True;
True `Not` False;
`<= a b` p:
  `Cmp a b` o.
  `~ o` p.

  `~ GT` False;
  `~ EQ` True;
  `~ LT` True;
`>= a b` p: `<= b a` p.
`< a b` p:
  `<= b a` p'.
  p' `Not` p.
`> a b` p:
  `<= a b` p'.
  p' `Not` p.

`BinaryArithmetic`:
  [] `~Succ` ['1];
  ['0 m . ms] `~Succ` ['1 m . ms];
  ['1 . m] `~Succ` ['0 . m']:
    m `~~Succ` m'.

  [] `~Pop` '0 [];
  ['0 m . ms] `~Pop` '0 [m . ms];
  ['1 . ms] `~Pop` '1 ms;

  m `~+ []` m;
  ms `~+ ['0 . n]` [m . ms'']:
    ms `~~Pop` m ms'.
    ms' `~~+ n` ms''.
  m `~+ ['1 . n]` [m' . ms']:
    m `~~Succ` [m' . ms].
    ms `~~+ n` ms'.

  (Binary m) `+ (Binary n)` (Binary m'):
    m `~~+ n` m'.

  a b `~Zip` abs:
    ! ~Go a b [] = ~Go [] [] abs.

    -- convert two little endian numbers to a zipped big endian number
    ~Go [] ['0 b' . bs]         abs = ~Go [] [b' . bs] [(, '0 '0) . abs];
    ~Go ['0 a' . as] []         abs = ~Go [a' . as] [] [(, '0 '0) . abs];
    ~Go [] ['1 . bs]            abs = ~Go [] bs [(, '0 '1) . abs];
    ~Go ['1 . as] []            abs = ~Go as [] [(, '1 '0) . abs];
    ~Go ['1] [b b' . bs]        abs = ~Go [] [b' . bs] [(, '1 b) . abs];
    ~Go [a a' . as] ['1]        abs = ~Go [a' . as] [] [(, a '1) . abs];
    ~Go ['1] ['1]               abs = ~Go [] [] [(, '1 '1) . abs];
    ~Go [a a' . as] [b b' . bs] abs = ~Go [a' . as] [b' . bs] [(, a b) . abs];

  `~Cmp a b` o:
    a b `~~Zip` abs.
    ! ~Go abs [] = ~Go abs [] o.

    -- check prefix of zipped big endian numbers
    ~Go [(, '0 '0) . abs] abs' = ~Go abs [(, '0 '0) . abs'];
    ~Go [(, '1 '1) . abs] abs' = ~Go abs [(, '1 '1) . abs'];
    ~Go [(, '0 '1) . abs] abs' = ~Go [(, '0 '1) . abs] abs' LT;
    ~Go [(, '1 '0) . abs] abs' = ~Go [(, '1 '0) . abs] abs' GT;
    ~Go [] abs' = ~Go [] abs' EQ;
    -- unwind prefix
    ~Go abs [(, '0 '0) . abs'] o = ~Go [(, '0 '0) . abs] abs' o;
    ~Go abs [(, '1 '1) . abs'] o = ~Go [(, '1 '1) . abs] abs' o;

  `Cmp (Binary a) (Binary b)` o:
    `~~Cmp a b` o.

  a b `~Diff` o d m:
    `~~Cmp a b` o.
    a b `~ o` d m.

    a b `~ EQ` [] a:
      `Dup a` b.
    a b `~ LT` d a:
      d `~~~+ a` b.
    a b `~ GT` d b:
      d `~~~+ b` a.

  (Binary a) (Binary b) `Diff` o (Binary d) (Binary m):
    a b `~~Diff` o d m.

  n `~QuoRem d` q r:
    ! ~Go n d Z = ~Go n d' m True.
    ! ~Go' n d' m [] = ~Go' r d Z q.

    -- find largest value of m such that 2^m d <= n
    ~Go n d m = ~Go n d m p:
      `< (Binary n) (Binary d)` p.
    ~Go n d m False = ~Go n ['0 . d] (S m);

    -- while 2^m d <= n, increment q, decrement m, and subtract 2^m d from n
    ~Go' n ['0 . d'] (S m) q = ~Go' n d' m q p:
      `<= (Binary d') (Binary n)` p.
    ~Go' n d' m q True = ~Go' n' d' m ['1 . q]:
      n' `~~~+ d'` n.
    ~Go' n d' m q False = ~Go' n d' m ['0 . q];

  (Binary n) `QuoRem (Binary d)` (Binary q) (Binary r):
    n `~~QuoRem d` q r.

  (Binary b) `Bin=Nat` n:
    ! ~Go n [] = ~Go Z b.
    ~Go (S n) b = ~Go n [b' . bs]:
      b `~~~Succ` [b' . bs].

  (Binary []) `Digits (Binary b)` [Z];
  (Binary [n . ns]) `Digits (Binary b)` [(S d) . ds]:
      ! ~Go b [n . ns] [] = ~Go b [] [(S d) . ds].
        ~Go b [n . ns] ds = ~Go b q [d . ds]:
            [n . ns] `~~~QuoRem b` q r.
            (Binary r) `Bin=Nat` d.

[]       `Map f` [];
[x . xs] `Map f` [y . ys]:
  x  `f`     y.
  xs `Map f` ys.

0  `Dig=Char` '0; 1  `Dig=Char` '1; 2  `Dig=Char` '2; 3  `Dig=Char` '3;
4  `Dig=Char` '4; 5  `Dig=Char` '5; 6  `Dig=Char` '6; 7  `Dig=Char` '7;
8  `Dig=Char` '8; 9  `Dig=Char` '9; 10 `Dig=Char` 'a; 11 `Dig=Char` 'b;
12 `Dig=Char` 'c; 13 `Dig=Char` 'd; 14 `Dig=Char` 'e; 15 `Dig=Char` 'f;

`DefaultBase` (Binary "0101");
n `Positional` str:
  `DefaultBase` b.
  n `Positional b` str.
n `Positional b` str:
  n `Digits b` ds.
  ds `Map Dig=Char` str.

[x . xs] `+ [y . ys]` [z . zs]:
  a `Positional` [x . xs].
  b `Positional` [y . ys].
  c `Positional` [z . zs].
  a `+ b` c.

[x . xs] `QuoRem [y . ys]` [z . zs] [w . ws]:
  n `Positional` [x . xs].
  d `Positional` [y . ys].
  q `Positional` [z . zs].
  r `Positional` [w . ws].
  n `QuoRem d` q r.

-- fetch a zero from an arbitrary number representation
`ZeroFrom n` z:
  `Dup n` n'.
  z `+ n` n'.

a `* b` c:
  c `QuoRem b` a r.
  `ZeroFrom b` r.
