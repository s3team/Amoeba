open Visit
open Type
open Pp_print
open Ail_utils

type instr_update = SUB | INSERT

class bb_opaque_diversify =
  (* A basic block opaque predicate diversity implementation.
   *
     Opaque Predicate Insertion: A single-predeceossor block /b/ can be
       substituted with a conditional branch to /b/ and its clone /b/' using
       arbitrary predicate.  these predicates can also guard blocks of garbage
       code so they never execute.
   *)

  let dec_hex (s:int) : string =
    "0x"^(Printf.sprintf "%X" s) in

  object(self)

    val mutable fb_tbl = Hashtbl.create 40
    val mutable instrs_update = []
    val mutable locs_update = []

    inherit ailVisitor

    method insert_instrs i l =
      instrs_update <- List.rev_append (List.rev instrs_update) [(i, l, INSERT, "")]

    method sub_instrs i l i' =
      let i_s = pp_print_instr i' in
      instrs_update <- List.rev_append (List.rev instrs_update) [(i, l, SUB, i_s)]

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
                      i::(help t_u (h::t))
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

    method update_current_bb b spt_pos =
      let bn = b.bblock_name in
      let bil = self#bb_instrs b in
      let i = List.nth bil spt_pos in
      let iloc = get_loc i in
      let iloc' = {iloc with loc_label = ""} in
      let i1 = DoubleInstr (StackOP PUSH, Reg (CommonReg EAX), iloc, None) in
      let i2 = DoubleInstr (ControlOP CALL, Label ("opaque_func"), iloc', None) in
      let i3 = TripleInstr (CommonOP (Compare CMPL), Reg (CommonReg EAX),
                            Const (Normal 0), iloc', None) in
      let i4 = DoubleInstr (ControlOP (Jump JE), Label (bn^"_opaque_next"), iloc', None) in
      let i5 = DoubleInstr (ControlOP CALL, Label ("halt_func"), iloc', None) in
      let i6 =
        DoubleInstr (StackOP (POP), Reg (CommonReg EAX),
                     {iloc with loc_label = (bn^"_opaque_next:")}, None) in
      let i0 = set_loc i {iloc with loc_label = ""} in
      self#sub_instrs i0 iloc i;
      self#insert_instrs i1 iloc;
      self#insert_instrs i2 iloc;
      self#insert_instrs i3 iloc;
      self#insert_instrs i4 iloc;
      self#insert_instrs i5 iloc;
      self#insert_instrs i6 iloc

    method print_bb_opaque b =
      print_string "basic block opaque transformation : ";
      print_string b.bblock_name;
      print_string " ";
      print_string (dec_hex b.bblock_begin_loc.loc_addr);
      print_string " ";
      print_string (dec_hex b.bblock_end_loc.loc_addr);
      print_string "\n"

    method update_bb n bl =
      let b = List.nth bl n in
      let spt_pos = 0 in
      (* self#print_bb_opaque b; *)
      self#update_current_bb b spt_pos;
      (* self#update_process; *)
      ()

    (*
   *)

    method bb_div_opaque =
      let rand_num n max =
        let n' = ref 0 in
        while !n' = n do
          n' := Random.int max;
        done;
        !n'
      in
      let help f bl =
        let len = List.length bl in
        if len > 1 then
          (
            (* let n = rand_num (-1) (len-1) in *)
            let n = Random.int len in
            self#update_bb n bl;
            ()
          )
        else
          () in
      print_string "bb opaque transformation on : ";
      print_int (Hashtbl.length fb_tbl);
      print_string "\n";
      Hashtbl.iter help fb_tbl;
      self#update_process


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

    method attach_opaque_routines =
      let last_i = List.nth instrs (List.length instrs - 1) in
      let last_loc = get_loc last_i in
(*
      self#opaque_func_insert last_loc;
      self#halt_func_insert last_loc;
      self#update_process
*)
	self#helper_insert last_loc

    method bb_opaque_process =
      self#bb_div_opaque;
      self#attach_opaque_routines;
      instrs;





    method opaque_func_insert iloc =
      let i1 =
        DoubleInstr (StackOP PUSH, Reg (StackReg EBP), {iloc with loc_label = ("opaque_func:")}, None) in
      let i2 = TripleInstr (CommonOP (Assign MOV), Reg (StackReg EBP),
                            Reg (StackReg ESP), iloc, None) in
      let i3 = TripleInstr (CommonOP (Assign MOV), Reg (CommonReg EAX),
                            Const (Normal 0), iloc, None) in
      let i4 = DoubleInstr (StackOP POP, Reg (StackReg EBP), iloc, None) in
      let i5 = SingleInstr (ControlOP RET, iloc, None) in
      self#insert_instrs i1 iloc;
      self#insert_instrs i2 iloc;
      self#insert_instrs i3 iloc;
      self#insert_instrs i4 iloc;
      self#insert_instrs i5 iloc

    (* this function helps to insert halt function *)
    (*
        halt_func:
              hlt
      *)
    method halt_func_insert iloc =
      let i1 =
        SingleInstr (CommonOP (Other HLT), {iloc with loc_label = ("halt_func:")}, None) in
      self#insert_instrs i1 iloc


    method helper_insert iloc =
      let iloc = {iloc with loc_label = ""} in
      let i1 =
        DoubleInstr (StackOP PUSH, Reg (StackReg EBP), {iloc with loc_label = ("opaque_func:")}, None) in
      let i2 = TripleInstr (CommonOP (Assign MOV), Reg (StackReg EBP),
                            Reg (StackReg ESP), iloc, None) in
      let i3 = TripleInstr (CommonOP (Assign MOV), Reg (CommonReg EAX),
                            Const (Normal 0), iloc, None) in
      let i4 = DoubleInstr (StackOP POP, Reg (StackReg EBP), iloc, None) in
      let i5 = SingleInstr (ControlOP RET, iloc, None) in
      let i6 =
        SingleInstr (CommonOP (Other HLT), {iloc with loc_label = ("halt_func:")}, None) in
      instrs <- List.rev_append (List.rev instrs) [i1;i2;i3;i4;i5;i6];


    method visit (il : instr list) : instr list =
      instrs <- il;
      self#bb_opaque_process


    method set_fb_tbl (fb : (string, Type.bblock list) Hashtbl.t ) : unit =
      fb_tbl <- fb

  end
