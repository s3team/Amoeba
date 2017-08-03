open Visit
open Type
open Pp_print
open Ail_utils

type instr_update = SUB | INSERT

class bb_split_diversify =
  (* A basic block split diversity implementation.
   *
   *
   *
   * *)
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
      let bil = self#bb_instrs b in
      let bn = b.bblock_name in
      let i = List.nth bil spt_pos in
      let iloc = get_loc i in
      let i1 =
        DoubleInstr (ControlOP (Jump JMP),
                     Label (bn^"_split"), {iloc with loc_label = ""}, None)
      and i2 =
        SingleInstr (CommonOP (Other NOP), {iloc with loc_label = (bn^"_split:")}, None) in
      self#insert_instrs i1 iloc;
      self#insert_instrs i2 iloc

    method print_bb_split b =
      print_string "reorder basic block : ";
      print_string b.bblock_name;
      print_string " ";
      print_string (dec_hex b.bblock_begin_loc.loc_addr);
      print_string " ";
      print_string (dec_hex b.bblock_end_loc.loc_addr);
      print_string "\n"

    method split_bb n bl =
      let rand_pos max =
        match max with
        | (-1) -> failwith "wired, in spli_bb"
        | 0 -> 0
        | _ -> Random.int max
      in
      let b = List.nth bl n in
      let bil = self#bb_instrs b in
      let il_len = List.length bil in
      let spt_pos = rand_pos (il_len-1) in
      self#update_current_bb b spt_pos;
      (* self#update_process; *)
      ()

    (*
     *)
    method bb_div_split =
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
            let n = rand_num (-1) len in
            self#split_bb n bl;
            ()
          )
        else
          () in
      print_string "bb split : ";
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
                                   loc_visible = true;} in
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
      self#bb_div_split;
      instrs;


    method visit (il : instr list) : instr list =
      print_string "start bb merge \n";
      instrs <- il;
      self#bb_div_process


    method set_fb_tbl (fb : (string, Type.bblock list) Hashtbl.t ) : unit =
      fb_tbl <- fb

  end
