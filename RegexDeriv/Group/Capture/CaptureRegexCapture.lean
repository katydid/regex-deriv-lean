-- This algorithm is based on the algorithm in RegexDeriv.Group.GroupCapture.
-- It has been adjust to store the capture information in a new matched operator.

import RegexDeriv.Group.Capture.CaptureRegex

namespace CaptureRegexCapture

-- see RegexDeriv.Group.GroupCapture.neutralize for original.
def neutralize (x: CaptureRegex): CaptureRegex :=
  match x with
  | CaptureRegex.emptyset => CaptureRegex.emptyset
  | CaptureRegex.epsilon => CaptureRegex.epsilon
  -- matched is handled exactly the same as epsilon, by simply preserving itself and the matched value.
  | CaptureRegex.matched c => CaptureRegex.matched c
  | CaptureRegex.char _ => CaptureRegex.emptyset
  | CaptureRegex.or y z => CaptureRegex.smartOr (neutralize y) (neutralize z)
  | CaptureRegex.concat y z => CaptureRegex.concat (neutralize y) (neutralize z)
  | CaptureRegex.star y => CaptureRegex.star (neutralize y)
  | CaptureRegex.group id y => CaptureRegex.group id (neutralize y)

partial def derive (x: CaptureRegex) (char: Char): CaptureRegex :=
  match x with
  | CaptureRegex.emptyset => CaptureRegex.emptyset
  | CaptureRegex.epsilon => CaptureRegex.emptyset
  | CaptureRegex.matched _ => CaptureRegex.emptyset
  | CaptureRegex.char char' =>
    if char' = char
    -- Unlike RegexDeriv.Group.GroupCapture.derive we do not return epsilon, but rather the matched char.
    then CaptureRegex.matched char
    else CaptureRegex.emptyset
  | CaptureRegex.or y z => CaptureRegex.smartOr (derive y char) (derive z char)
  | CaptureRegex.concat y z =>
    if CaptureRegex.nullable y
    then CaptureRegex.smartOr
      (CaptureRegex.smartConcat (derive y char) z)
      (CaptureRegex.smartConcat (neutralize y) (derive z char))
    else CaptureRegex.concat (derive y char) z
  | CaptureRegex.star y => CaptureRegex.smartConcat (derive y char) x
  -- Unlike RegexDeriv.Group.GroupCapture.derive we do not store the captured char here, but rather in matched.
  | CaptureRegex.group id y =>
    CaptureRegex.group id (derive y char)

-- extract extracts a single list of characters for the whole expression.
-- This based on extractGroups, but only returns one captured string.
def extract (x: CaptureRegex): List Char :=
  match x with
  | CaptureRegex.emptyset => []
  | CaptureRegex.epsilon => []
  | CaptureRegex.char _ => []
  -- Unlike extractGroups, matched returns the single matched character.
  | CaptureRegex.matched c => [c]
  | CaptureRegex.or y z =>
    if y.nullable
    then extract y
    else extract z
  | CaptureRegex.concat y z =>
    extract y ++ extract z
  | CaptureRegex.star _ => []
    -- Unlike extractGroups we ignore this group, since we aren't interested in capturing it's string right now.
    -- This embedded group will be extracted later by extractGroups.
  | CaptureRegex.group _ y => extract y

-- extractGroups returns the captured string for each group.
def extractGroups (x: CaptureRegex): List (Nat × List Char) :=
  match x with
  | CaptureRegex.emptyset => []
  | CaptureRegex.epsilon => []
  | CaptureRegex.char _ => []
  -- matched is the same epsilon and acts accordingly.
  | CaptureRegex.matched _ => []
  | CaptureRegex.or y z =>
    if y.nullable
    then extractGroups y
    else extractGroups z
  | CaptureRegex.concat y z =>
    extractGroups y ++ extractGroups z
  | CaptureRegex.star _ => []
    -- Unlike RegexDeriv.Group.GroupCapture.extractGroups group no longer contains the string.
    -- We need to extract the string from the expression.
  | CaptureRegex.group id y => (id, extract y) :: extractGroups y

-- captures returns all captured strings for all groups.
def captures (x: CaptureRegex) (str: String): Option (List (Nat × String)) :=
  match str with
  | String.mk chars =>
  let dx := List.foldl derive x chars
  if dx.nullable
  then
    let ex := extractGroups dx
    Option.some (List.map (fun(id, cs) => (id, String.mk cs) ) ex)
  else Option.none

-- capture only returns the longest capture for a specific group.
def capture (name: Nat) (x: CaptureRegex) (str: String): Option String :=
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

#guard capture 1 (CaptureRegex.concat (CaptureRegex.concat
    (CaptureRegex.star (CaptureRegex.char 'a'))
    (CaptureRegex.group 1 (CaptureRegex.char 'b')))
    (CaptureRegex.star (CaptureRegex.char 'a'))
  )
  "aaabaaa" =
  Option.some "b"

#guard captures (CaptureRegex.concat (CaptureRegex.concat
    (CaptureRegex.star (CaptureRegex.char 'a'))
    (CaptureRegex.group 1 (CaptureRegex.char 'b')))
    (CaptureRegex.star (CaptureRegex.char 'a'))
  )
  "aaabaaa" =
  Option.some [(1, "b")]

#guard capture 1 (CaptureRegex.concat (CaptureRegex.concat
    (CaptureRegex.star (CaptureRegex.char 'a'))
    (CaptureRegex.group 1 (CaptureRegex.star (CaptureRegex.char 'b'))))
    (CaptureRegex.star (CaptureRegex.char 'a'))
  )
  "aaabbbaaa" =
  Option.some "bbb"

#guard captures (CaptureRegex.concat (CaptureRegex.concat
    (CaptureRegex.star (CaptureRegex.char 'a'))
    (CaptureRegex.group 1 (CaptureRegex.star (CaptureRegex.char 'b'))))
    (CaptureRegex.star (CaptureRegex.char 'a'))
  )
  "aaabbbaaa" =
  Option.some [(1, "bbb")]

#guard capture 1 (CaptureRegex.concat (CaptureRegex.concat
    (CaptureRegex.star (CaptureRegex.char 'a'))
    (CaptureRegex.group 1
      (CaptureRegex.or
        (CaptureRegex.star (CaptureRegex.char 'b'))
        (CaptureRegex.star (CaptureRegex.char 'c'))
      )
    ))
    (CaptureRegex.star (CaptureRegex.char 'a'))
  )
  "aaacccaaa" =
  Option.some "ccc"

#guard capture 1 (CaptureRegex.concat (CaptureRegex.concat
    (CaptureRegex.star (CaptureRegex.char 'a'))
    (CaptureRegex.group 1
      (CaptureRegex.or
        (CaptureRegex.star (CaptureRegex.char 'b'))
        (CaptureRegex.concat (CaptureRegex.char 'b') (CaptureRegex.star (CaptureRegex.char 'c')))
      )
    ))
    (CaptureRegex.star (CaptureRegex.char 'a'))
  )
  "aaabccaaa" =
  Option.some "bcc"

#guard captures
  (CaptureRegex.group 1
    (CaptureRegex.star
      (CaptureRegex.or
        (CaptureRegex.char 'a')
        (CaptureRegex.concat (CaptureRegex.char 'a') (CaptureRegex.char 'a'))
      )
    )
  )
  "aaa" =
  Option.some [(1, "aaa")]

#guard captures
  (CaptureRegex.star
    (CaptureRegex.group 1
      (CaptureRegex.or
        (CaptureRegex.char 'a')
        (CaptureRegex.concat (CaptureRegex.char 'a') (CaptureRegex.char 'a'))
      )
    )
  )
  "aaa" =
  Option.some [(1, "aa"), (1, "a")]

#guard captures
  (CaptureRegex.star
    (CaptureRegex.group 1
      (CaptureRegex.or
        (CaptureRegex.char 'a')
        (CaptureRegex.concat (CaptureRegex.char 'a') (CaptureRegex.char 'a'))
      )
    )
  )
  "aaaa" =
  Option.some [(1, "aa"), (1, "aa")]
