-- Experimental capturing with the not operator.

namespace CaptureNotRegex

inductive CaptureNotRegex where
  -- emptyset captures a string that was not matched.
  | emptyset (s: Option Char)
  -- epsilon captures a character that was matched.
  | epsilon (c: Option Char)
  | char (c: Char)
  -- any is a useful operator for creating a contains combinator, which is useful for testing the not operator.
  | any
  | or (y z: CaptureNotRegex)
  | and (y z: CaptureNotRegex)
  | concat (y z: CaptureNotRegex)
  | interleave (y z: CaptureNotRegex)
  | star (y: CaptureNotRegex)
  | group (id: Nat) (x: CaptureNotRegex)
  -- not is the compliment operator.
  | not (y: CaptureNotRegex)
  -- a neutralized expression preserves captured characters, but stops capturing more.
  | neutralized (y: CaptureNotRegex)
  deriving DecidableEq, Ord, Repr, Hashable

def CaptureNotRegex.nullable (x: CaptureNotRegex): Bool :=
  match x with
  | CaptureNotRegex.emptyset _ => false
  | CaptureNotRegex.epsilon _ => true
  | CaptureNotRegex.char _ => false
  | CaptureNotRegex.any => false
  | CaptureNotRegex.or y z => nullable y || nullable z
  | CaptureNotRegex.and y z => nullable y && nullable z
  | CaptureNotRegex.concat y z => nullable y && nullable z
  | CaptureNotRegex.interleave y z => nullable y && nullable z
  | CaptureNotRegex.star _ => true
  -- The group is nullable if its embedded expression is nullable.
  | CaptureNotRegex.group _ y => nullable y
  | CaptureNotRegex.not y => ! (nullable y)
  -- neutralized should calculate the nullablitily of its child expression.
  -- Yes neutralized starts out as nullable, but that can change, even if not more characters are captured.
  | CaptureNotRegex.neutralized y => nullable y

def CaptureNotRegex.isEmptySetCapture (x: CaptureNotRegex): Bool :=
  match x with
  | CaptureNotRegex.emptyset _ => true
  | CaptureNotRegex.concat y z => isEmptySetCapture y && isEmptySetCapture z
  | _ => false

-- contains is a combinator to create a contains expression.
def CaptureNotRegex.contains (x: CaptureNotRegex): CaptureNotRegex :=
  (concat (star any) (concat x (star any)))

-- smartOr is a smart constructor for the or operator.
def CaptureNotRegex.smartOr (x y: CaptureNotRegex): CaptureNotRegex :=
  match x with
  | emptyset Option.none => y
  | _ =>
    match y with
    | emptyset Option.none => x
    | _ => or x y

-- smartConcat is a smart constructor for the concat operator.
def CaptureNotRegex.smartConcat (x y: CaptureNotRegex): CaptureNotRegex :=
  match x with
  | emptyset Option.none => emptyset Option.none
  | epsilon Option.none => y
  | _ =>
    match y with
    | emptyset Option.none => emptyset Option.none
    | epsilon Option.none => x
    | _ => concat x y

-- smartStar is a smart constructor for the star operator.
def CaptureNotRegex.smartStar (x: CaptureNotRegex): CaptureNotRegex :=
  match x with
  | emptyset Option.none => epsilon Option.none
  | star _ => x
  | _ => star x

-- smartNot is a smart constructor for the not operator.
def CaptureNotRegex.smartNot (x: CaptureNotRegex): CaptureNotRegex :=
  match x with
  | not y => y
  | _ => not x

-- cap says whether the derivative should capture, i.e. the expression is not neutralized.
partial def derive (cap: Bool) (x: CaptureNotRegex) (char: Char): CaptureNotRegex :=
  match x with
  | CaptureNotRegex.emptyset Option.none =>
    if cap
    -- keep a list of the unmatched characters.
    then CaptureNotRegex.emptyset char
    else CaptureNotRegex.emptyset Option.none
  | CaptureNotRegex.emptyset (Option.some c) =>
    if cap
    -- keep a list of the unmatched characters.
    then CaptureNotRegex.concat (CaptureNotRegex.emptyset c) (CaptureNotRegex.emptyset char)
    else CaptureNotRegex.emptyset (Option.some c)
  | CaptureNotRegex.epsilon Option.none =>
    if cap
    then CaptureNotRegex.emptyset (Option.some char)
    else CaptureNotRegex.emptyset Option.none
  | CaptureNotRegex.epsilon (Option.some c) =>
    if cap
    then CaptureNotRegex.concat (CaptureNotRegex.emptyset c) (CaptureNotRegex.emptyset char)
    else CaptureNotRegex.emptyset (Option.some c)
  | CaptureNotRegex.char c =>
    if cap
    then
      if c = char
      -- keep the matched character.
      then CaptureNotRegex.epsilon (Option.some char)
      else CaptureNotRegex.emptyset (Option.some char)
    else
      CaptureNotRegex.emptyset Option.none
  | CaptureNotRegex.any =>
    if cap
    then CaptureNotRegex.epsilon (Option.some char)
    else CaptureNotRegex.emptyset Option.none
  | CaptureNotRegex.or y z => CaptureNotRegex.smartOr (derive cap y char) (derive cap z char)
  | CaptureNotRegex.and y z => CaptureNotRegex.and (derive cap y char) (derive cap z char)
  | CaptureNotRegex.concat y z =>
    if CaptureNotRegex.nullable y
    then CaptureNotRegex.smartOr
      (CaptureNotRegex.smartConcat (derive cap y char) z)
      (CaptureNotRegex.smartConcat (CaptureNotRegex.neutralized y) (derive cap z char))
    else
      if CaptureNotRegex.isEmptySetCapture x
      then
        -- If this is not correct then revert emptyset to capture a list characters.
        -- We prefer this way, since now it is easier to generalize beyond strings to trees.
        -- In derive, if y = emptyset or a concat of emptyset, then the order is usually mixed up in `CaptureNotRegex.concat (derive cap y char) z`
        -- But if this is a concat of emptysets, then it doesn't matter which derivative we take, so we might as well take the second derivative to preserve the capturing order.
        CaptureNotRegex.concat y (derive cap z char)
      else CaptureNotRegex.concat (derive cap y char) z
  | CaptureNotRegex.interleave y z =>
    CaptureNotRegex.smartOr
      (CaptureNotRegex.interleave (derive cap y char) z)
      (CaptureNotRegex.interleave y (derive cap z char))
  | CaptureNotRegex.star y => CaptureNotRegex.smartConcat (derive cap y char) x
  | CaptureNotRegex.group id y =>
    CaptureNotRegex.group id (derive cap y char)
  | CaptureNotRegex.not y =>
    CaptureNotRegex.smartNot (derive cap y char)
  | CaptureNotRegex.neutralized y =>
    -- neutralized expressions do not capture any more characters, but preserve the capture information they have.
    CaptureNotRegex.neutralized (derive false y char)

-- extract extracts a single list of characters for the whole expression.
-- This based on extractGroups, but only returns one captured string.
-- The neg := false, only return characters in epsilon
--     neg := true, only return characters in emptyset
def extract (neg: Bool) (x: CaptureNotRegex): List Char :=
  match x with
  | CaptureNotRegex.emptyset c =>
    if neg
    then c.toList
    else []
  | CaptureNotRegex.epsilon c =>
    if neg
    then []
    else c.toList
  | CaptureNotRegex.char _ => []
  | CaptureNotRegex.any => []
  | CaptureNotRegex.or y z =>
    -- TODO: Need examples that test whether this should be
    -- if y.nullable
    -- OR
    -- if y.nullable && !neg
    if y.nullable
    then extract neg y
    else extract neg z
  | CaptureNotRegex.and y z =>
    let ey := extract neg y
    let ez := extract neg z
    if ey == ez
    then ey
    else []
  | CaptureNotRegex.concat y z =>
    extract neg y ++ extract neg z
  | CaptureNotRegex.interleave y z =>
    extract neg y ++ extract neg z
  | CaptureNotRegex.star _ => []
  | CaptureNotRegex.group _ y => extract neg y
  -- not inverts the neg value, to make sure we capture the unmatched or matched if it was a double negation.
  | CaptureNotRegex.not y => extract (!neg) y
  | CaptureNotRegex.neutralized y => extract neg y

-- extractGroups returns the captured string for each group.
def extractGroups (neg: Bool) (x: CaptureNotRegex): List (Nat × List Char) :=
  match x with
  | CaptureNotRegex.emptyset _ => []
  | CaptureNotRegex.epsilon _ => []
  | CaptureNotRegex.char _ => []
  | CaptureNotRegex.any => []
  | CaptureNotRegex.or y z =>
    -- TODO: Need examples that test whether this should be
    -- if y.nullable
    -- OR
    -- if y.nullable && !neg
    if y.nullable
    then extractGroups neg y
    else extractGroups neg z
  | CaptureNotRegex.and y z =>
    extractGroups neg y ++ extractGroups neg z
  | CaptureNotRegex.concat y z =>
    extractGroups neg y ++ extractGroups neg z
  | CaptureNotRegex.interleave y z =>
    extractGroups neg y ++ extractGroups neg z
  | CaptureNotRegex.star _ => []
  | CaptureNotRegex.group id y => (id, extract neg y) :: extractGroups neg y
  -- not inverts the neg value, to make sure we capture the unmatched or matched if it was a double negation.
  | CaptureNotRegex.not y => extractGroups (!neg) y
  | CaptureNotRegex.neutralized y => extractGroups neg y

-- captures returns all captured strings for all groups.
def captures (x: CaptureNotRegex) (str: String): Option (List (Nat × String)) :=
  match str with
  | String.mk chars =>
  -- derive true, because the default should be to want capturing.
  let dx := List.foldl (derive true) x chars
  if dx.nullable
  then
    -- extractGroups false, since the default is not neg.
    let ex := extractGroups false dx
    Option.some (List.map (fun(id, cs) => (id, String.mk cs) ) ex)
  else Option.none

-- capture only returns the longest capture for a specific group.
def capture (name: Nat) (x: CaptureNotRegex) (str: String): Option String :=
  match captures x str with
  | Option.none => Option.none
  | Option.some cs =>
  let strs := List.filterMap
    (fun (name', str') =>
      if name = name'
      then Option.some str'
      else Option.none
    ) cs
  List.head? (List.reverse (List.mergeSort strs))

-- # Tests

open CaptureNotRegex (emptyset epsilon char any or and concat interleave star group not contains)

-- ## New Interleave Tests

#guard capture 1 (interleave
    (char 'a')
    (group 1 (char 'b'))
  )
  "ab"
  = Option.some "b"

#guard capture 1 (interleave
    (char 'a')
    (group 1 (char 'b'))
  )
  "ba"
  = Option.some "b"

#guard capture 1 (interleave
    (concat (char 'a') (char 'b'))
    (group 1 (concat (char 'c') (char 'd')))
  )
  "abcd"
  = Option.some "cd"

#guard capture 1 (interleave
    (concat (char 'a') (char 'b'))
    (group 1 (concat (char 'c') (char 'd')))
  )
  "acbd"
  = Option.some "cd"

#guard capture 1 (interleave
    (concat (char 'a') (char 'b'))
    (group 1 (concat (char 'c') (char 'd')))
  )
  "acdb"
  = Option.some "cd"

#guard capture 1 (interleave
    (concat (char 'a') (char 'b'))
    (group 1 (concat (char 'c') (char 'd')))
  )
  "cadb"
  = Option.some "cd"

#guard capture 1 (interleave
    (concat (char 'a') (char 'b'))
    (group 1 (concat (char 'c') (char 'd')))
  )
  "cabd"
  = Option.some "cd"

#guard capture 1 (interleave
    (concat (char 'a') (char 'b'))
    (group 1 (concat (char 'c') (char 'd')))
  )
  "cdab"
  = Option.some "cd"

#guard capture 1 (interleave
    (star (char 'a'))
    (group 1 (char 'b'))
  )
  "aaabaaa"
  = Option.some "b"

#guard capture 1 (interleave
    (star (char 'a'))
    (group 1 (star (char 'b')))
  )
  "aaababaa"
  = Option.some "bb"

-- ### Old Concat Tests adjusted for Interleave

#guard capture 1 (interleave (interleave
    (star (char 'a'))
    (group 1 (char 'b')))
    (star (char 'a'))
  )
  "aaabaaa"
  = Option.some "b"

#guard captures (interleave (interleave
    (star (char 'a'))
    (group 1 (char 'b')))
    (star (char 'a'))
  )
  "aaabaaa"
  = Option.some [(1, "b")]

#guard capture 1 (interleave (interleave
    (star (char 'a'))
    (group 1 (star (char 'b'))))
    (star (char 'a'))
  )
  "aaabbbaaa"
  = Option.some "bbb"

#guard captures (interleave (interleave
    (star (char 'a'))
    (group 1 (star (char 'b'))))
    (star (char 'a'))
  )
  "aaabbbaaa"
  = Option.some [(1, "bbb")]

#guard capture 1 (interleave (interleave
    (star (char 'a'))
    (group 1
      (or
        (star (char 'b'))
        (star (char 'c'))
      )
    ))
    (star (char 'a'))
  )
  "aaacccaaa"
  = Option.some "ccc"

#guard capture 1 (interleave (interleave
    (star (char 'a'))
    (group 1
      (or
        (star (char 'b'))
        (interleave (char 'b') (star (char 'c')))
      )
    ))
    (star (char 'a'))
  )
  "aaabccaaa"
  = Option.some "bcc"

#guard captures
  (group 1
    (star
      (or
        (char 'a')
        (interleave (char 'a') (char 'a'))
      )
    )
  )
  "aaa"
  = Option.some [(1, "aaa")]

#guard captures
  (star
    (group 1
      (or
        (char 'a')
        (interleave (char 'a') (char 'a'))
      )
    )
  )
  "aaa"
  = Option.some [(1, "aa"), (1, "a")]

#guard captures
  (star
    (group 1
      (or
        (char 'a')
        (interleave (char 'a') (char 'a'))
      )
    )
  )
  "aaaa"
  = Option.some [(1, "aa"), (1, "aa")]


-- ## New And Tests

#guard capture 1
  (group 1 (and (char 'b') (char 'b')))
  "b"
  = Option.some "b"

#guard capture 1
  (group 1 (and (not (char 'a')) (char 'b')))
  "b"
  = Option.some "b"

#guard capture 1
  (group 1 (and (not (char 'a')) (not (char 'c'))))
  "b"
  = Option.some "b"

#guard capture 1
  (group 1 (and (not (char 'a')) (not (char 'c'))))
  "bb"
  = Option.some "bb"

#guard capture 1
  (and (group 1 (not (char 'a'))) (not (char 'c')))
  "bb"
  = Option.some "bb"

#guard capture 1
  (and (group 1 (not (char 'a'))) (star (char 'b')))
  "bb"
  = Option.some "bb"

#guard capture 1
  (and (group 1 (not (char 'a'))) (star (char 'c')))
  "bb"
  = Option.none

#guard capture 1
  (group 1 (and (not (char 'a')) (star (char 'c'))))
  "bb"
  = Option.none

-- ## New Not Tests

#guard capture 1
  (group 1 (not (char 'b')))
  "a"
  = Option.some "a"

#guard capture 1
  (group 1 (not (not (char 'b'))))
  "b"
  = Option.some "b"

#guard capture 1
  (group 1 (not (char 'b')))
  "aa"
  = Option.some "aa"

#guard capture 1
  (group 1 (or
    (not (char 'b'))
    (not (char 'a'))
  ))
  "aa"
  = Option.some "aa"

#guard capture 1
  (group 1 (or
    (not (char 'b'))
    (char 'a')
  ))
  "a"
  = Option.some "a"

#guard capture 1
  (group 1 (or
    (not (char 'b'))
    (concat (char 'a') (char 'a'))
  ))
  "aa"
  = Option.some "aa"

#guard capture 1
  (group 1 (or
    (not (char 'b'))
    (contains (char 'a'))
  ))
  "aa"
  = Option.some "aa"

-- The next few are tests for the order of extraction.
#guard capture 1
  (group 1
    (not (char 'a'))
  )
  "abc"
  = Option.some "abc"

#guard capture 1
  (group 1 (or
    (not (char 'a'))
    (contains (char 'a'))
  ))
  "aab"
  = Option.some "aab"

#guard capture 1
  (group 1
    (not (char 'a'))
  )
  "abcd"
  = Option.some "abcd"

#guard capture 1
  (group 1
    (not (char 'a'))
  )
  "abcde"
  = Option.some "abcde"

#guard capture 1
  (group 1
    (not (char 'a'))
  )
  "abcdef"
  = Option.some "abcdef"

#guard capture 1
  (group 1
    (not (concat (char 'a') (char 'b')))
  )
  "abcdef"
  = Option.some "abcdef"

#guard capture 1
  (concat
    (char 'a')
    (group 1 (not (char 'a')))
  )
  "ab"
  = Option.some "b"

#guard capture 1
  (concat
    (group 1 (not (char 'a')))
    (group 2 (char 'a'))
  )
  "ba"
  = Option.some "b"

#guard capture 2
  (concat
    (group 1 (not (char 'a')))
    (group 2 (char 'a'))
  )
  "ba"
  = Option.some "a"

#guard capture 1
  (concat
    (star (char 'a'))
    (concat
      (group 1 (not (contains (char 'a'))))
      (star (char 'a'))
    )
  )
  "aba"
  = Option.some "b"

#guard capture 1
  (group 1 (contains (char 'b')))
  "aaaabaaa"
  = Option.some "aaaabaaa"

#guard capture 1
  (group 1 (not (contains (char 'b'))))
  "aaaabaaa"
  = Option.none

#guard capture 1
  (group 1 (contains (char 'a')))
  "aaaabaaa"
  = Option.some "aaaabaaa"

#guard capture 1
  (group 1 (not (contains (char 'a'))))
  "aaaabaaa"
  = Option.none

#guard capture 1
  (group 1 (not (contains (char 'a'))))
  "b"
  = Option.some "b"

#guard capture 1
  (concat
    (star (char 'a'))
    (group 1 (not (contains (char 'a'))))
  )
  "aaab"
  = Option.some "b"

#guard capture 1
  (concat
    (group 1 (not (contains (char 'a'))))
    (star (char 'a'))
  )
  "ba"
  = Option.some "b"

#guard captures
  (concat
    (group 1 (not (contains (char 'a'))))
    (star (char 'a'))
  )
  "baa"
  = [(1, "b")]

#guard captures
  (concat
    (group 1 (not
      (concat (star any) (char 'a'))
    ))
    (star (char 'a'))
  )
  "baa"
  = [(1, "b")]

#guard captures
  (concat
    (group 1 (not
      (concat (star any) (char 'a'))
    ))
    (star (char 'a'))
  )
  "baaa"
  = [(1, "b")]

#guard captures
  (concat
    (star (char 'a'))
    (concat
      (group 1 (not (contains (char 'a'))))
      (star (char 'a'))
    )
  )
  "aaabaaa"
  = [(1, "b")]

-- Remember not b includes aa and not just a
#guard capture 1
  (not (group 1 (char 'b')))
  "aa"
  = Option.some "aa"

#guard capture 1 (concat
    (star (char 'a'))
    (group 1 (not (char 'a'))))
  "aab"
  = Option.some "b"

#guard capture 1 (concat
    (star (char 'a'))
    (group 1 (not (char 'a'))))
  "aab"
  = Option.some "b"

-- Remmeber not a is ba, not just b
#guard capture 1 (concat (concat
    (star (char 'a'))
    (group 1 (not (char 'a'))))
    (star (char 'a'))
  )
  "aaba"
  = Option.some "ba"

#guard capture 1 (concat (concat
    (star (char 'a'))
    (group 1 (not (char 'a'))))
    (star (char 'a'))
  )
  "aaba"
  = Option.some "ba"

#guard capture 1 (concat (concat
    (star (char 'a'))
    (group 1 (not (char 'a'))))
    (star (char 'a'))
  )
  "aaba"
  = Option.some "ba"

#guard capture 1 (concat (concat
    (star (char 'a'))
    (group 1 (not (not (char 'b')))))
    (star (char 'a'))
  )
  "aaabaaa"
  = Option.some "b"

#guard capture 1 (concat (concat
    (star (char 'a'))
    (group 1 (not (not (contains (char 'b'))))))
    (star (char 'a'))
  )
  "aaabaaa"
  = Option.some "baaa"

#guard capture 1 (concat (concat
    (star (char 'a'))
    (group 1 (not (not (contains (char 'b'))))))
    (star (char 'a'))
  )
  "aaaabaaaa"
  = Option.some "baaaa"

#guard capture 1 (concat (concat
    (star (char 'a'))
    (group 1 (contains (char 'b'))))
    (star (char 'a'))
  )
  "aaabaaa"
  = Option.some "baaa"

-- ## Old Tests without Not

#guard capture 1 (concat (concat
    (star (char 'a'))
    (group 1 (char 'b')))
    (star (char 'a'))
  )
  "aaabaaa"
  = Option.some "b"

#guard captures (concat (concat
    (star (char 'a'))
    (group 1 (char 'b')))
    (star (char 'a'))
  )
  "aaabaaa"
  = Option.some [(1, "b")]

#guard capture 1 (concat (concat
    (star (char 'a'))
    (group 1 (star (char 'b'))))
    (star (char 'a'))
  )
  "aaabbbaaa"
  = Option.some "bbb"

#guard captures (concat (concat
    (star (char 'a'))
    (group 1 (star (char 'b'))))
    (star (char 'a'))
  )
  "aaabbbaaa"
  = Option.some [(1, "bbb")]

#guard capture 1 (concat (concat
    (star (char 'a'))
    (group 1
      (or
        (star (char 'b'))
        (star (char 'c'))
      )
    ))
    (star (char 'a'))
  )
  "aaacccaaa"
  = Option.some "ccc"

#guard capture 1 (concat (concat
    (star (char 'a'))
    (group 1
      (or
        (star (char 'b'))
        (concat (char 'b') (star (char 'c')))
      )
    ))
    (star (char 'a'))
  )
  "aaabccaaa"
  = Option.some "bcc"

#guard captures
  (group 1
    (star
      (or
        (char 'a')
        (concat (char 'a') (char 'a'))
      )
    )
  )
  "aaa"
  = Option.some [(1, "aaa")]

#guard captures
  (star
    (group 1
      (or
        (char 'a')
        (concat (char 'a') (char 'a'))
      )
    )
  )
  "aaa"
  = Option.some [(1, "aa"), (1, "a")]

#guard captures
  (star
    (group 1
      (or
        (char 'a')
        (concat (char 'a') (char 'a'))
      )
    )
  )
  "aaaa"
  = Option.some [(1, "aa"), (1, "aa")]
