-- This algorithm is from Regular Expression Sub-Matching using Partial Derivatives - Martin Sulzmann and Kenny Zhuo Ming Lu

-- Thank you Keegan Perry for simplifying and explaining this to me.
import RegexDeriv.Group.GroupRegex

namespace GroupRegexCapture

-- neutralize replaces all char operators with emptyset.
-- It is used when deriving concat.
-- This way we do not lose capture information on nullable expressions.
def neutralize (x: GroupRegex): GroupRegex :=
  match x with
  | GroupRegex.emptyset => GroupRegex.emptyset
  | GroupRegex.epsilon => GroupRegex.epsilon
  -- only char changes to emptyset
  | GroupRegex.char _ => GroupRegex.emptyset
  | GroupRegex.or y z => GroupRegex.smartOr (neutralize y) (neutralize z)
  | GroupRegex.concat y z => GroupRegex.concat (neutralize y) (neutralize z)
  | GroupRegex.star y => GroupRegex.star (neutralize y)
  | GroupRegex.group id c y => GroupRegex.group id c (neutralize y)

partial def derive (x: GroupRegex) (char: Char): GroupRegex :=
  match x with
  | GroupRegex.emptyset => GroupRegex.emptyset
  | GroupRegex.epsilon => GroupRegex.emptyset
  | GroupRegex.char char' =>
    if char' = char
    then GroupRegex.epsilon
    else GroupRegex.emptyset
  | GroupRegex.or y z => GroupRegex.smartOr (derive y char) (derive z char)
  | GroupRegex.concat y z =>
    if GroupRegex.nullable y
    then GroupRegex.smartOr
      (GroupRegex.smartConcat (derive y char) z)
      -- A difference from the usual derive algorithm:
      -- Instead of (derive z char), we write:
      (GroupRegex.smartConcat (neutralize y) (derive z char))
    else GroupRegex.concat (derive y char) z
  | GroupRegex.star y => GroupRegex.smartConcat (derive y char) x
  -- group is the new operator compared to Regex.
  -- We store the input char in the expression.
  | GroupRegex.group id chars y =>
    GroupRegex.group id (chars ++ [char]) (derive y char)

-- extractGroups returns the captured string for each group.
def extractGroups (x: GroupRegex): List (Nat × List Char) :=
  match x with
  -- should never be encountered, since emptyset is not nullable.
  | GroupRegex.emptyset => []
  | GroupRegex.epsilon => []
  -- should never be encountered, since char is not nullable.
  | GroupRegex.char _ => []
  | GroupRegex.or y z =>
    -- Under POSIX semantics, we prefer matching the left alternative.
    if y.nullable
    then extractGroups y
    else extractGroups z
  | GroupRegex.concat y z =>
    extractGroups y ++ extractGroups z
    -- Groups under a star are ignored.
    -- Recursively extracting under the star causes empty captures to be reported,
    -- which we do not want under POSIX semantics.
  | GroupRegex.star _ => []
  | GroupRegex.group id c y => (id, c) :: extractGroups y

-- captures returns all captured strings for all groups.
def captures (x: GroupRegex) (str: String): Option (List (Nat × String)) :=
  match str with
  | String.mk chars =>
  let dx := List.foldl derive x chars
  if dx.nullable
  then
    let ex := extractGroups dx
    Option.some (List.map (fun(id, cs) => (id, String.mk cs) ) ex)
  else Option.none

-- capture only returns the longest capture for a specific group.
def capture (name: Nat) (x: GroupRegex) (str: String): Option String :=
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

#guard capture 1 (GroupRegex.concat (GroupRegex.concat
    (GroupRegex.star (GroupRegex.char 'a'))
    (GroupRegex.group 1 [] (GroupRegex.char 'b')))
    (GroupRegex.star (GroupRegex.char 'a'))
  )
  "aaabaaa" =
  Option.some "b"

#guard captures (GroupRegex.concat (GroupRegex.concat
    (GroupRegex.star (GroupRegex.char 'a'))
    (GroupRegex.group 1 [] (GroupRegex.char 'b')))
    (GroupRegex.star (GroupRegex.char 'a'))
  )
  "aaabaaa" =
  Option.some [(1, "b")]

#guard capture 1 (GroupRegex.concat (GroupRegex.concat
    (GroupRegex.star (GroupRegex.char 'a'))
    (GroupRegex.group 1 [] (GroupRegex.star (GroupRegex.char 'b'))))
    (GroupRegex.star (GroupRegex.char 'a'))
  )
  "aaabbbaaa" =
  Option.some "bbb"

#guard captures (GroupRegex.concat (GroupRegex.concat
    (GroupRegex.star (GroupRegex.char 'a'))
    (GroupRegex.group 1 [] (GroupRegex.star (GroupRegex.char 'b'))))
    (GroupRegex.star (GroupRegex.char 'a'))
  )
  "aaabbbaaa" =
  Option.some [(1, "bbb")]

#guard capture 1 (GroupRegex.concat (GroupRegex.concat
    (GroupRegex.star (GroupRegex.char 'a'))
    (GroupRegex.group 1 []
      (GroupRegex.or
        (GroupRegex.star (GroupRegex.char 'b'))
        (GroupRegex.star (GroupRegex.char 'c'))
      )
    ))
    (GroupRegex.star (GroupRegex.char 'a'))
  )
  "aaacccaaa" =
  Option.some "ccc"

#guard capture 1 (GroupRegex.concat (GroupRegex.concat
    (GroupRegex.star (GroupRegex.char 'a'))
    (GroupRegex.group 1 []
      (GroupRegex.or
        (GroupRegex.star (GroupRegex.char 'b'))
        (GroupRegex.concat (GroupRegex.char 'b') (GroupRegex.star (GroupRegex.char 'c')))
      )
    ))
    (GroupRegex.star (GroupRegex.char 'a'))
  )
  "aaabccaaa" =
  Option.some "bcc"

#guard captures
  (GroupRegex.group 1 []
    (GroupRegex.star
      (GroupRegex.or
        (GroupRegex.char 'a')
        (GroupRegex.concat (GroupRegex.char 'a') (GroupRegex.char 'a'))
      )
    )
  )
  "aaa" =
  Option.some [(1, "aaa")]

#guard captures
  (GroupRegex.star
    (GroupRegex.group 1 []
      (GroupRegex.or
        (GroupRegex.char 'a')
        (GroupRegex.concat (GroupRegex.char 'a') (GroupRegex.char 'a'))
      )
    )
  )
  "aaa" =
  Option.some [(1, "aa"), (1, "a")]

#guard captures
  (GroupRegex.star
    (GroupRegex.or
      (GroupRegex.char 'b')
      (GroupRegex.group 1 []
        (GroupRegex.or
          (GroupRegex.char 'a')
          (GroupRegex.concat (GroupRegex.char 'a') (GroupRegex.char 'a'))
        )
      )
    )
  )
  "aaaa" =
  Option.some [(1, "aa"), (1, "aa")]

#guard captures
  (GroupRegex.star
    (GroupRegex.or
      (GroupRegex.char 'b')
      (GroupRegex.group 1 []
        (GroupRegex.or
          (GroupRegex.char 'a')
          (GroupRegex.concat (GroupRegex.char 'a') (GroupRegex.char 'a'))
        )
      )
    )
  )
  "aabbaa" =
  Option.some [(1, "aa"), (1, "aa")]
