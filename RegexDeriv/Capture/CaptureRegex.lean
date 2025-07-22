-- CaptureRegex includes capturing groups, via the new matched and group operator.
inductive CaptureRegex where
  | emptyset
  | epsilon
  -- Unlike RegexDeriv.Group.GroupRegex.GroupRegex the matched operator is new.
  -- matched will act like epsilon, but contain the character that it matched.
  | matched (c: Char)
  | char (c: Char)
  | or (y z: CaptureRegex)
  | concat (y z: CaptureRegex)
  | star (y: CaptureRegex)
  -- Unlike RegexDeriv.Group.GroupRegex.GroupRegex this group does not contain the captured string.
  | group (id: Nat) (x: CaptureRegex)
  deriving DecidableEq, Ord, Repr, Hashable

def CaptureRegex.nullable (x: CaptureRegex): Bool :=
  match x with
  | CaptureRegex.emptyset => false
  | CaptureRegex.epsilon => true
  -- matched is technically the same as epsilon, so it is also nullable.
  | CaptureRegex.matched _ => true
  | CaptureRegex.char _ => false
  | CaptureRegex.or y z => nullable y || nullable z
  | CaptureRegex.concat y z => nullable y && nullable z
  | CaptureRegex.star _ => true
  -- The group is nullable if its embedded expression is nullable.
  | CaptureRegex.group _ y => nullable y

-- unescapable returns whether this expression will not change based on any input.
-- For example, emptyset will never change based on any input, so it will return true.
def CaptureRegex.unescapable (x: CaptureRegex): Bool :=
  match x with
  | CaptureRegex.emptyset => true
  | _ => false

-- smartOr is a smart constructor for the or operator.
def CaptureRegex.smartOr (x y: CaptureRegex): CaptureRegex :=
  match x with
  | CaptureRegex.emptyset => y
  | _ =>
    match y with
    | CaptureRegex.emptyset => x
    | _ => CaptureRegex.or x y

-- smartConcat is a smart constructor for the concat operator.
def CaptureRegex.smartConcat (x y: CaptureRegex): CaptureRegex :=
  match x with
  | CaptureRegex.emptyset => CaptureRegex.emptyset
  | _ =>
    match y with
    | CaptureRegex.emptyset => CaptureRegex.emptyset
    | _ => CaptureRegex.concat x y

-- smartStar is a smart constructor for the star operator.
def CaptureRegex.smartStar (x: CaptureRegex): CaptureRegex :=
  match x with
  | CaptureRegex.star _ => x
  | _ => CaptureRegex.star x
