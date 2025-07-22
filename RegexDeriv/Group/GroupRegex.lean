-- GroupRegex includes capturing groups
inductive GroupRegex where
  | emptyset
  | epsilon
  | char (c: Char)
  | or (y z: GroupRegex)
  | concat (y z: GroupRegex)
  | star (y: GroupRegex)
  -- group is the only new operator compared to a GroupRegex without capturing groups.
  | group (id: Nat) (capture: List Char) (x: GroupRegex)
  deriving DecidableEq, Ord, Repr, Hashable

def GroupRegex.nullable (x: GroupRegex): Bool :=
  match x with
  | GroupRegex.emptyset => false
  | GroupRegex.epsilon => true
  | GroupRegex.char _ => false
  | GroupRegex.or y z => nullable y || nullable z
  | GroupRegex.concat y z => nullable y && nullable z
  | GroupRegex.star _ => true
  -- The group is nullable if its embedded expression is nullable.
  | GroupRegex.group _ _ y => nullable y

def GroupRegex.unescapable (x: GroupRegex): Bool :=
  match x with
  | GroupRegex.emptyset => true
  | _ => false

-- smartOr is a smart constructor for the or operator.
def GroupRegex.smartOr (x y: GroupRegex): GroupRegex :=
  match x with
  | GroupRegex.emptyset => y
  | _ =>
    match y with
    | GroupRegex.emptyset => x
    | _ => GroupRegex.or x y

-- smartConcat is a smart constructor for the concat operator.
def GroupRegex.smartConcat (x y: GroupRegex): GroupRegex :=
  match x with
  | GroupRegex.emptyset => GroupRegex.emptyset
  | _ =>
    match y with
    | GroupRegex.emptyset => GroupRegex.emptyset
    | _ => GroupRegex.concat x y

-- smartStar is a smart constructor for the star operator.
def GroupRegex.smartStar (x: GroupRegex): GroupRegex :=
  match x with
  | GroupRegex.star _ => x
  | _ => GroupRegex.star x
