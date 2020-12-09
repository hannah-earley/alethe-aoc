import "lib.al";
magic "io.file.read" `Read path` contents;
magic "data.any.dup" `Dup' orig` copy;
magic "data.any.eq" `Eq' x y` p;

x `Id` x;

xs `Rev` ys:
  ! ~Go xs [] = ~Go [] ys.
    ~Go [x . xs] ys = ~Go xs [x . ys];

ys `Split x` zss':
  ! ~Go x ys [] [] = ~Go x [] zs zss.
  zs `Rev` zs'.
  [zs' . zss] `Rev` zss'.

  ~Go x [y . ys] zs zss = ~Go x [y . ys] zs zss p:
    `Eq' x y` p.
  ~Go x [y . ys] zs zss True = ~Go x ys [] [zs' . zss]:
    `Dup' x` y.
    zs `Rev` zs'.
  ~Go x [y . ys] zs zss False = ~Go x ys [y . zs] zss;

text `Lines` lines:
  text `Split #"'\n"` lines.

`Contains haystack needle` p:
  `Dup p'` p.
  ! ~Go haystack [] needle False = ~Go' h h' y p'.
    ~Go [x . xs] xs' y False = ~Go xs [x . xs'] y p:
      `Eq' x y` p.
    ~Go [] xs' y False = ~Go' [] xs' y False;
    ~Go xs [x . xs'] y True = ~Go' [x . xs] xs' y True;

`Day1a'` r':
  sum `Id` "2020".
  `Read "1.txt"` c.
  c `Lines` lines.
  `Dup r` r'.

  ! ~Go sum lines [] Nothing = ~Go sum l l' (Just r).
    ~Go sum [l . ls] ls' Nothing = ~Go sum ls [l . ls'] r:
      k `+ l` sum.
      `Contains ls k` p.
      p `~ k l` r.

      False `~ k l` Nothing;
      True `~ k l` (Just (, k' l' kl)):
        `Dup l` l'.
        `Dup k` k'.
        `Dup k` k''.
        k'' `* l` kl.

`Day1` r1' r2':
  `~Data` sum nums.
  `~Data` sum nums:
    sum `Positional` "2020".
    `Read "1.txt"` c.
    c `Lines` lines.
    nums `Map Positional` lines.

  `~1 r1` r1'.
  `~1 (Just (, k l))` (, k' l' kl):
    `Dup k` k'.
    `Dup k` k''.
    `Dup l` l'.
    k'' `* l'` kl.

  `~2 r2` r2'.
  `~2 (Just (, j k l))` (, j' k' l' jkl):
    `Dup j` j'.
    `Dup j` j''.
    `Dup k` k'.
    `Dup l` l'.
    j'' `* k'` jk.
    jk `* l'` jkl.


  ! ~Go1 sum nums [] Nothing = ~Go1' sum l1 l1' r1.
    ~Go1 sum [] ls' Nothing = ~Go1' sum [] ls' Nothing;
    ~Go1 sum [l . ls] ls' (Just r) = ~Go1' sum [l . ls] ls' (Just r);
    ~Go1 sum [l . ls] ls' Nothing = ~Go1 sum ls [l . ls'] r:
      `< l sum` valid.
      `~1 valid l ls sum` r.

      `~1 False l ls sum` Nothing;
      `~1 True l ls sum` r:
        k `+ l` sum.
        `Contains ls k` p.
        p `~~2 k l` r.

      False `~2 k l` Nothing;
      True `~2 k l` (Just (, kp lp)):
        `Dup (, k l)` (, k' l').
        k' `Positional` kp.
        l' `Positional` lp.


  ! ~Go2 sum nums [] Nothing = ~Go2' sum l2 l2' r2.
    ~Go2 sum [] ls' Nothing = ~Go2' sum [] ls' Nothing;
    ~Go2 sum [l . ls] ls' (Just r) = ~Go2' sum [l . ls] ls' (Just r);
    ~Go2 sum [l . ls] ls' Nothing = ~Go2 sum ls [l . ls'] r:
      `< l sum` valid.
      `~1 valid l ls sum` r.

      `~1 False l ls sum` Nothing;
      `~1 True l ls sum` r:
        k `+ l` sum.
        ~~~Go1 k ls [] Nothing = ~~~Go1' k l1 l2 r'.
        `Dup r'` r''.
        r'' `~~2 l` r.

      Nothing `~2 l` Nothing;
      (Just (, j k)) `~2 l` (Just (, j k lp)):
        `Dup l` l'.
        l' `Positional` lp.
