open Batteries

open Visit
open Type
open Pp_print

open Ail_utils

type instr_update = SUB | INSERT

class instr_replace_diversify =
(* A instruction replace insertion diversity implementation.
 *
 *  
 *
 *   
 *   
 *  
 *  
 * *)
object(self)

  val mutable instrs_update = []

  inherit ailVisitor

  method insert_instrs i l =
    (* instrs_update <- instrs_update@[(i, l, INSERT, "")] *)
    instrs_update <- (i, l, INSERT, "")::instrs_update

  method sub_instrs i l i' =
    let i_s = pp_print_instr i' in
    (* instrs_update <- instrs_update@[(i, l, SUB, i_s)] *)
    instrs_update <- (i, l, SUB, i_s)::instrs_update


      method update_instrs instrs =
        let same loc1 loc2 =
          loc1.loc_addr = loc2.loc_addr in
        let rec help l_u l acc =
          match (l_u, l) with
          | (h_u::t_u, h::t) ->
            begin
              let (i, loc1, ty, i_s) = h_u
              and loc2 = get_loc h in
                if same loc1 loc2 then
                  begin
                    match ty with
                    | SUB ->
                      begin
                        let h_s = pp_print_instr h in
                        if i_s = h_s then
                            (help t_u (i::t) acc)
                        else
                          help l_u t (h::acc)
                      end
                    | INSERT ->
                        help t_u (h::t) (i::acc)
                  end
                else
                  help l_u t (h::acc)
            end
          | ([], l') -> List.rev_append acc l'
          | (h::t, []) ->
            begin
              failwith "error in update_instrs"
            end
        in
          help instrs_update instrs []


  method bb_instrs b =
    let bloc = b.bblock_begin_loc
    and eloc = b.bblock_end_loc in
    let rec help il acc =
      match il with
      | h::t ->
         begin
           let loc = get_loc h in
           if loc.loc_addr >= bloc.loc_addr &&
                loc.loc_addr <= eloc.loc_addr then
             help t (h::acc)
           else help t acc
         end
      | [] -> List.rev acc in
    help instrs []



  (*
   *)
  method instr_replace =
    let random_bool =
      let n = Random.int 10 in
        if n < 11 then true
        else false in
    let is_call op =
        match op with
        | ControlOP c ->
          begin
            match c with
              | CALL -> true
              | _ -> false
          end
        | _ -> false in
    let is_ret op =
      match op with
      | ControlOP c ->
         begin
           match c with
           | RET | RETN -> true
           | _ -> false
         end
      | _ -> false
    and is_xor_reg op e1 e2 =
      let is_reg e1 e2 =
        match e1, e2 with
        | Reg r1, Reg r2 ->
           begin
             let s1 = Show.show<reg> r1
             and s2 = Show.show<reg> r2 in
             if s1 = s2 then true
             else false
           end
        | _ -> false
      and is_xor op =
        match op with
        | CommonOP c ->
           begin
             match c with
             | Logic c' ->
                begin
                  match c' with
                  | XOR -> true
                  | _ -> false
                end
             | _ -> false
           end
        | _ -> false in
      let isxor = is_xor op
      and isreg = is_reg e1 e2 in
      if (isxor = true)&&(isreg = true) then true
      else false in
      let is_shl_reg op e1 e2 =
          let is_reg e1 =
            match e1 with
            | Reg _ -> true
            | _ -> false
          and is_num e2 =
            match e2 with
            | Const _ -> true
            | _ -> false
          and is_shl op =
            match op with
            | CommonOP c ->
              begin
               match c with
                | Rol c' ->
                  begin
                    match c' with
                    | SHL -> true
                    | _ -> false
                  end
                | _ -> false
              end
            | _ -> false in
          let isxor = is_shl op
          and isnum = is_num e2
          and isreg = is_reg e1 in
          if (isxor = true)&&(isreg = true)&&(isnum = true)
          then true else false in
    let help i =
      match i with
      | SingleInstr (p, l, _) when (is_ret p) ->
         self#update_ret i l
      | DoubleInstr (p, e, l, _) when (is_call p) -> 
      	self#update_call i e l 
      | TripleInstr (p, e1, e2, l, _) when (is_xor_reg p e1 e2) ->
         self#update_xor i e1 l
      | _ -> () in
    List.iter help instrs

  (* 
   * 
   *)
  method update_ret i l =
    let l1 = l
    and l2 = {l with loc_label = ""} in
    let i2 =
      DoubleInstr (StackOP POP, Reg (CommonReg ECX), l1, None)
    and i1 =
      DoubleInstr (ControlOP (Jump JMP), Symbol (StarDes (Reg (CommonReg ECX))), l2, None) in
    self#sub_instrs i1 l i;
    self#insert_instrs i2 l

  (*
   *
   * *)


  method update_call i e l =
    let help i e l =
      let jmp_label = "S_"^(dec_hex l.loc_addr)^"_next" in
      let l1 = {l with loc_label = ""} in
      let i2 =
        DoubleInstr (StackOP PUSH, Label ("$"^jmp_label), l, None)
      and i3 =
        DoubleInstr (ControlOP (Jump JMP), e, l1, None) in
      let i3_str = "jmp "^(p_exp e)^"\n" in
      let i1 =
        SingleInstr (CommonOP (Other NOP), {l with loc_label = i3_str^jmp_label^": "}, None) in
      self#sub_instrs i1 l i ;
      self#insert_instrs i2 l in
    match e with
    (*
    *)
    | Symbol (StarDes _) -> ()
    | Symbol s ->
       begin
         match s with
         | CallDes f ->
            if f.is_lib = false then (help i e l)
            else  ()
         | _ -> help i e l
       end
    | Label s -> help i e l
    | _ -> failwith "unsupport call"


  (*
   *  
   *)
  method update_xor i e l =
    let i' = TripleInstr (CommonOP (Assign MOV), e,
                          Const (Normal 0), l, None) in
    self#sub_instrs i' l i



  method update_shl i e1 e2 l =
    let n =
      match e2 with
      | Const c ->
         begin
           match c with
           | Normal n -> n
           | _ -> failwith "update_shl"
         end
      | _ -> failwith "update_shl" in
    let v = Int.pow 2 n in
    let i' = TripleInstr (CommonOP (Arithm MUL),
                          Const (Normal v), e1,l, None) in
    self#sub_instrs i' l i


  method update_process =
    instrs_update <-
      List.sort (
          fun (_,l1,_,_) (_,l2,_,_) ->
          l1.loc_addr - l2.loc_addr
        ) instrs_update;

    instrs <- self#update_instrs instrs;
    instrs_update <- []

  method instr_div_process =
	print_string "instr replace start\n";
    self#instr_replace;
    self#update_process;
    instrs;

  method visit (il : instr list) : instr list =
    instrs <- il;
    self#instr_div_process

end
