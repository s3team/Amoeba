open Batteries

open Visit
open Type
open Pp_print
open Ail_utils


type instr_update = SUB | INSERT

class bb_branchfunc_diversify =

  (* A control flow branch function diversity implementation.
   *
   * the assumption that the call function returns to the instruction
  immmediately following the call instruction can be exploited using branch
  functions.


   A branch function /f/ is a function that, whenever it is called from one of
   the locations a, causes control to be transferred to the corresponding
   location /b/. Given such a branch function we can replace /n/ conditional
   statements by the following lines.

    A1: jmp b1
    A2: jmp b2
    An: jmp bn


   A1: call f
   A2: call f
   An: call f

   *
   *)

  let dec_hex (s:int) : string =
    "0x"^(Printf.sprintf "%X" s) in

  object(self)

    val mutable fb_tbl = Hashtbl.create 40
    val mutable cfg_t = []
    val mutable funcs_list = []
    val mutable funcs_assoc = []
    val mutable instrs_update = []
    val mutable locs_update = []

    inherit ailVisitor

    method insert_instrs i l =
      instrs_update <- List.rev_append (List.rev instrs_update) [(i, l, INSERT, "")]

    method sub_instrs i l i' =
      let i_s = pp_print_instr i' in
      instrs_update <- List.rev_append (List.rev instrs_update) [(i, l, SUB, i_s)]

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
                        help t_u (t) (i::h::acc)
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

    method update_instrs_abd instrs =
      let same loc1 loc2 =
        loc1.loc_addr = loc2.loc_addr in
      let rec help l_u l =
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
                        begin
                          (help t_u (i::t))
                        end
                      else
                        h::(help l_u t)
                    end
                 | INSERT ->
                    begin
                      h::(help t_u (i::t))
                    end
               end
             else
               h::(help l_u t)
           end
        | ([], l') -> l'
        | (h::t, []) ->
           begin
             failwith "error in update_instrs"
           end
      in
      help instrs_update instrs


    method print_bb_branch f =
      print_string "branch cfg for function : ";
      print_string f;
      print_string "\n"

    (*
     *)
    method branch_func =
      let aux f =

        (* self#print_bb_branch f; *)

        let func = List.assoc f funcs_assoc in
        let fil = f_instrs func instrs in
        List.iter (
            fun i ->
            match get_op i with
            | ControlOP (Jump JMP) ->
               begin
                 match get_cf_des i with
                 | Some (Label s) ->
                    let l = get_loc i in
                    let i0 = TripleInstr (CommonOP (Assign MOVL), Label "branch_des",
                                          Label ("$"^s), l, None) in
                    let i1 =
                      DoubleInstr (ControlOP CALL,
                                   Label ("branch_routine"), {l with loc_label = ""}, None) in
                    self#sub_instrs i0 l i;
                    self#insert_instrs i1 l;
                    self#update_process;
                 | _ -> ()
               end
            | _ -> ()
          ) fil in
      print_string "bb branch on ";
      print_int (List.length funcs_list);
      print_string " candiadate functions\n";
      List.iter aux funcs_list



    (*
     * branch all jmp!
     *)
    method bb_div_branch =
      self#branch_func;


    method update_locs instrs =
      locs_update <- List.rev locs_update;
      let rec help il ll acc =
        match (il, ll) with
        | (ih::it, lh::lt) ->
           begin
             let lo = get_loc ih in
             if lo.loc_addr = lh.loc_addr then
               begin
                 let ih' = set_loc ih
                                   {loc_label = lo.loc_label^"\n"^lh.loc_label;
                                    loc_addr = lo.loc_addr;
                                    loc_visible = true;
                                   } in
                 help it lt (ih'::acc)
               end
             else
               (
                 help it ll (ih::acc)
               )
           end
        | (il', []) -> List.rev_append acc il'
        | ([], ll') -> failwith "error in update_locs" in
      help instrs locs_update []


    method update_process =
      instrs_update <-
        List.sort (
            fun (_,l1,_,_) (_,l2,_,_) ->
            l1.loc_addr - l2.loc_addr
          ) instrs_update;

      instrs <- self#update_instrs instrs;
      instrs_update <- []

    method bb_div_process =
      self#bb_div_branch;
      self#attach_branch_routine;
      instrs;

    method attach_branch_routine =
      let i = List.nth instrs (List.length instrs - 1) in
      let l = get_loc i in
      let i0 = DoubleInstr (StackOP (POP), Label "global_des",
                            {l with loc_label = "branch_routine :"}, None) in
      let i1 =
        DoubleInstr (ControlOP (Jump JMP),
                     Label "*branch_des", {l with loc_label = "branch_routine :"}, None) in
      instrs <- List.rev_append (List.rev instrs) [i0; i1];
      ()


    method visit (il : instr list) : instr list =
      print_string "start bb branch \n";
      instrs <- il;
      self#bb_div_process


    method set_fb_tbl (fb : (string, Type.bblock list) Hashtbl.t ) : unit =
      fb_tbl <- fb

    method set_cfg_tbl (tb : (string * (string * (Type.control * string option)
                                       ) list) list) : unit =
      cfg_t <- tb

    method set_funclist (fl : Type.func list) : unit =
      funcs_assoc <- List.map (
                         fun f ->
                         (f.func_name , f)
                       ) fl;
      funcs_list <- List.map ( fun f -> f.func_name) fl;

  end
