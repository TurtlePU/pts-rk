let rec nat = function 0 -> Execution.O | n -> Execution.S (nat (n - 1))
let rec int = function Execution.O -> 0 | Execution.S n -> 1 + int n
let () =
  let mode = int_of_string Sys.argv.(1) in
  if mode = 3 then
    Printf.printf "size5=%d size7=%d\n%!"
      (int (Execution.enumeration_count (nat 5)))
      (int (Execution.enumeration_count (nat 7)))
  else begin
    let checks = Execution.execute (nat mode) in
    List.iter (fun b -> Printf.printf "%b " b) checks;
    Printf.printf "\n%!";
    if not (List.for_all Fun.id checks) then exit 1
  end
