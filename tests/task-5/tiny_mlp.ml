open Category
module Make (C : sig
  include CartesianClosedCat
  val ok_float: float ok
  include NumCat
  with type t := float
  with type ('a, 'b) k := ('a, 'b) k
  include FloatingCat
  with type t := float
  with type ('a, 'b) k := ('a, 'b) k
end) = struct
  include CartesianCatDerivedOperations (C)
  open C
let t_1 = ok_float

let t_2 = (ok_pair t_1 t_1)

let t_3 = (ok_pair t_2 t_2)

let t_4 = id t_3

let t_5 = fork t_3 t_3 t_3

let t_6 = t_5 (t_4)

let t_7 = t_6 (t_4)

let t_8 = (ok_pair t_3 t_3)

let t_9 = it t_8

let t_10 = 0.

let t_11 = unit_arrow t_1

let t_12 = t_11 t_10

let t_13 = ok_unit

let t_14 = compose t_8 t_13 t_1

let t_15 = t_14 (t_12)

let t_16 = t_15 (t_9)

let t_17 = compose t_3 t_8 t_1

let t_18 = t_17 (t_16)

let t_19 = t_18 (t_7)

let t_20 = exr t_3 t_1

let t_21 = exl t_3 t_1

let t_22 = (ok_pair t_3 t_1)

let t_23 = id t_22

let t_24 = fork t_22 t_22 t_3

let t_25 = t_24 (t_23)

let t_26 = t_25 (t_21)

let t_27 = (ok_pair t_22 t_3)

let t_28 = it t_27

let t_29 = negC

let t_30 = compose t_13 t_1 t_1

let t_31 = t_30 t_29

let t_32 = t_31 (t_12)

let t_33 = compose t_27 t_13 t_1

let t_34 = t_33 (t_32)

let t_35 = t_34 (t_28)

let t_36 = compose t_22 t_27 t_1

let t_37 = t_36 (t_35)

let t_38 = t_37 (t_26)

let t_39 = fork t_22 t_1 t_1

let t_40 = t_39 (t_38)

let t_41 = t_40 (t_20)

let t_42 = addC

let t_43 = compose t_22 t_2 t_1

let t_44 = t_43 t_42

let t_45 = t_44 (t_41)

let t_46 = t_33 (t_12)

let t_47 = t_46 (t_28)

let t_48 = t_36 (t_47)

let t_49 = t_48 (t_26)

let t_50 = curry t_22 t_3 t_1

let t_51 = t_50 (t_47)

let t_52 = (ok_arrow t_3 t_1)

let t_53 = fork t_22 t_22 t_52

let t_54 = t_53 (t_23)

let t_55 = t_54 (t_51)

let t_56 = (ok_pair t_22 t_52)

let t_57 = fork t_22 t_56 t_22

let t_58 = t_57 (t_55)

let t_59 = t_58 (t_23)

let t_60 = (ok_pair t_56 t_22)

let t_61 = fork t_22 t_60 t_1

let t_62 = t_61 (t_59)

let t_63 = t_62 (t_20)

let t_64 = (ok_pair t_60 t_1)

let t_65 = fork t_22 t_64 t_1

let t_66 = t_65 (t_63)

let t_67 = t_66 (t_49)

let t_68 = (ok_pair t_64 t_1)

let t_69 = fork t_22 t_68 t_1

let t_70 = t_69 (t_67)

let t_71 = t_70 (t_45)

let t_72 = (ok_pair t_68 t_1)

let t_73 = it t_72

let t_74 = 0.5

let t_75 = t_11 t_74

let t_76 = compose t_72 t_13 t_1

let t_77 = t_76 (t_75)

let t_78 = t_77 (t_73)

let t_79 = compose t_22 t_72 t_1

let t_80 = t_79 (t_78)

let t_81 = t_80 (t_71)

let t_82 = t_39 (t_81)

let t_83 = t_82 (t_45)

let t_84 = mulC

let t_85 = t_43 t_84

let t_86 = t_85 (t_83)

let t_87 = t_39 (t_86)

let t_88 = t_87 (t_45)

let t_89 = t_85 (t_88)
let nn = C.(
t_19
)
let error = C.(
t_89
)
end
