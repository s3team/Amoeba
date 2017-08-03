open Visit
open Type
open Pp_print

open Ail_utils

type instr_update = SUB | INSERT

class instr_garbage_diversify =
(* A instruction garbage insertion diversity implementation.
 *
 *
* *)
    object(self)

      val mutable fb_tbl = Hashtbl.create 40
      val mutable instrs_update = []
      val mutable locs_update = []

      inherit ailVisitor

      method insert_instrs i l =
        (* instrs_update <- instrs_update@[(i, l, INSERT, "")] *)
        instrs_update <- (i, l, INSERT, "")::instrs_update

      method sub_instrs i l i' =
        let i_s = pp_print_instr i' in
        (* instrs_update <- instrs_update@[(i, l, SUB, i_s)] *)
        instrs_update <- (i, l, SUB, i_s)::instrs_update

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




      method garbage_produce loc =
        let n1 = Random.int 5 in
        let n2 = Random.int 5 in
        let n3 = Random.int 5 in
        let nop1 =
          SingleInstr (CommonOP (Other NOP), loc, None) in
        let nop2 =
          TripleInstr (CommonOP (Assign MOV), Reg (StackReg ESP),
                                 Reg (StackReg ESP), loc, None) in
        let nop3 =
          TripleInstr (CommonOP (Assign MOV), Reg (StackReg EBP),
                                 Reg (StackReg EBP), loc, None) in
        let nop4 =
          TripleInstr (CommonOP (Assign XCHG), Reg (StackReg EBP),
                                 Reg (StackReg EBP), loc, None) in
        let nop5 =
          TripleInstr (CommonOP (Assign XCHG), Reg (StackReg ESP),
                                 Reg (StackReg ESP), loc, None) in
        let l = [|nop1;nop2;nop3;nop4;nop5|] in
        let i1 = Array.get l n1 in
        let i2 = Array.get l n2 in
        let i3 = Array.get l n3 in
        [i1;i2;i3]

      (*
       *)
      method instr_insert_garbage =
        let rand_pos max =
          match max with
           | (-1) -> failwith "failed in rand_pos"
           | 0 -> 0
           | _ -> Random.int max
        in
        let insert_garbage il pos =
          let i = List.nth il pos in
            let iloc = get_loc i in
              let gl = self#garbage_produce {iloc with loc_label = ""} in
                List.iter (fun gi -> self#insert_instrs gi iloc) gl in
        let insert_bb b =
          let bil = self#bb_instrs b in
            let bil_len = List.length bil in
              let pos = rand_pos (bil_len-1) in
                insert_garbage bil pos in
        let insert_bbl bl =
          let bl_len = List.length bl in
          let pos = rand_pos (bl_len-1) in
          let b = List.nth bl pos in
          insert_bb b in
        let help f bl =
            insert_bbl bl in
        Hashtbl.iter help fb_tbl

      method update_process =
        instrs_update <-
        List.sort (
                fun (_,l1,_,_) (_,l2,_,_) ->
                  l1.loc_addr - l2.loc_addr
            ) instrs_update;

        instrs <- self#update_instrs instrs;
        instrs_update <- []

      method instr_div_process =
        self#instr_insert_garbage;
        self#update_process;
        instrs;

      method visit (il : instr list) : instr list =
        instrs <- il;
        self#instr_div_process

      method set_fb_tbl (fb : (string, Type.bblock list) Hashtbl.t ) : unit =
        fb_tbl <- fb

    end
