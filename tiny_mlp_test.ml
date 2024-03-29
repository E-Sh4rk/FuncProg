(** We need to evaluate [error] defined in [tiny_mlp.j]... *)
module Eval = Tiny_mlp.Make (Category.FloatLambdaCat)
(** ... and we also need the derivative of [error]. *)
module Diff = Tiny_mlp.Make (DiffCat)

(** We study a very small MLP with two inputs, one output
    and no hidden layer. *)
type net = float * float

let make_net wxu wyu = (wxu, wyu)

let update_net (wxu, wyu) dwxu dwyu = make_net (wxu +. dwxu) (wyu +. dwyu)

(** A training set is a list of couples made of inputs and expected outputs. *)
type training_set = ((float * float) * float) list

(** A trained net must minimize the error function defined in tiny_mlp.j. *)
let acceptable_error = 0.01

let eval_net net training_set =
  List.map (fun (input, expectation) ->
      Eval.error ((input, net), expectation)
    ) training_set
  |> List.fold_left max min_float

let print_net (w1, w2) = Printf.printf "%f %f\n" w1 w2

(** [train training_set] returns a neural network trained for the
    [training_set]. *)
let train : training_set -> net = fun tset ->
  let eps = (* DiffCat.epsilon *) 1. in
  let res = ref (make_net (0.) (0.)) in
  let last_error = ref (eval_net !res tset) in
  while !last_error >= acceptable_error
  do
    let train_on tset =
      let (inputs,exp) = tset in
      let args = ((inputs, !res), exp) in
      let weight1 = (((0.,0.),(!last_error *. eps, 0.)),0.) in
      let weight2 = (((0.,0.),(0., !last_error *. eps)),0.) in
      let diff1 = DiffCat.epsilon_dapply Diff.error args weight1 in
      let diff2 = DiffCat.epsilon_dapply Diff.error args weight2 in
      res := update_net (!res) (-.diff1) (-.diff2)
    
    in List.iter train_on tset ;
    last_error := eval_net !res tset ;
    (*print_net !res ; Printf.printf "%f\n" (!last_error) ; *)
  done ;
  !res

let test =
  let training_set = [ (0., 1.), 0.; (1., 0.), 1. ] in
  let trained_net = train training_set in
  assert (eval_net trained_net training_set < acceptable_error)
