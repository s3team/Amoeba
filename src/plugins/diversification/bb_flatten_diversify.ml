open Batteries

open Visit
open Type
open Pp_print
open Ail_utils

type instr_update = SUB | INSERT

class bb_flatten_diversify =

  (* A basic block flattern diversity implementation.
   *
   * All edges between basic blocks : both conditional and unconditional - has
  been redirected to a dispatcher node which uses a new artificial variable to
  decide which block should be jumped to next.
   * the variable is updated at the end of each separated basic block.
   *
   *)

  let dec_hex (s:int) : string =
    "0x"^(Printf.sprintf "%X" s) in

  object(self)

    val mutable fb_tbl = Hashtbl.create 40
    (* how to choose the size ? *)
    val mutable cfg_t = []
    val mutable u_funcs = []
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


    method print_bb_flatten f =
      print_string "flatten cfg for function : ";
      print_string f;
      print_string "\n"

    (*
     
     *)
    method flatten_cfg cfg =
      let (f , _) = cfg in
      self#print_bb_flatten f;
      let bbl = Hashtbl.find fb_tbl f in
      let bnl = List.map (fun b -> b.bblock_name) bbl in
      let tl = List.map (
                   fun b ->
                   (b.bblock_name, b.bblock_end_loc)
                 ) bbl in
      List.iter (
          fun (n,l) ->
          let n1 = get_next_bb n in
          if List.mem n1 bnl then
            begin
              let i0 =
                DoubleInstr (ControlOP (Jump JMP),
                             Label (n1), {l with loc_label = ""}, None) in
              self#insert_instrs i0 l;
            end
          else ()
        ) tl;
      self#update_process;

      let func = List.assoc f u_funcs in
      let fil = f_instrs func instrs in
      List.iter (
          fun i ->
          match get_op i with
          | ControlOP (Jump j) ->
             begin
               match get_cf_des i with
               | Some (Label s) ->
                  let l = get_loc i in
                  let i0 = TripleInstr (CommonOP (Assign MOVL), Label "global_des",
                                        Label ("$"^s), l, None) in
                  let i1 =
                    DoubleInstr (ControlOP (Jump j),
                                 Label ("switch_bb"), {l with loc_label = ""}, None) in
                  self#sub_instrs i0 l i;
                  self#insert_instrs i1 l;
                  (* self#update_process; *)
               | _ -> ()
             end
          | _ -> ()
        ) fil;
       self#update_process;
	()



    (*
     *)
    method bb_div_flatten =
      let rand_num n max =
        let n' = ref 0 in
        while !n' = n do
          n' := Random.int max;
        done;
        !n'
      in
      let help cfgs =
        let len = List.length cfgs in
        if len > 0 then
          (
           (*  let n = rand_num (0) (len-1) in *)
            let n = Random.int len in
	print_string "random : ";
	print_int n;
	print_string "\n";
           (* let cfg = List.nth cfgs (n+6) in  *)
           let cfg = List.nth cfgs n in
            (* let cfg = List.nth cfgs 50 in *)
		self#flatten_cfg cfg;
            (* List.iter self#flatten_cfg cfgs; *)
            ()
          )
        else
          () in
      let cfgs = self#flattenable_cfg cfg_t in
      help cfgs

    (*
     *)
    method flattenable_cfg cfg_t =
      List.filter (
          fun (f, v) ->
          List.fold_left (
              fun acc t ->
              match (acc, t) with
              | (false, _) -> false
              | (_, (_, (_, None))) -> false
              | (_, (_, (_, Some(s)))) when s = "T" -> false
              | _ -> acc
            ) true v
        ) cfg_t


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
      self#bb_div_flatten;
      self#attach_switch_routine;
      instrs;

    method attach_switch_routine =
     (* let i = List.nth instrs (List.length instrs - 1) in *)
      let i = List.nth instrs 0 in
      let l = get_loc i in
      let i0 =
        DoubleInstr (ControlOP (Jump JMP),
                     Label " *global_des", {l with loc_label = ".globl switch_bb\nswitch_bb :"}, None) in
      let i1 =
          SingleInstr (CommonOP (Other NOP), {l with loc_label = ""}, None) in
      instrs <- List.rev_append (List.rev instrs) [i0];
      ()


    method visit (il : instr list) : instr list =
      instrs <- il;
      let r = self#bb_div_process in
	r


    method set_fb_tbl (fb : (string, Type.bblock list) Hashtbl.t ) : unit =
      fb_tbl <- fb

    method set_cfg_tbl (tb : (string * (string * (Type.control * string option)
                                       ) list) list) : unit =
      cfg_t <- tb

    method set_funclist (fl : Type.func list) : unit =
      u_funcs <- List.map (
                     fun f ->
                     (f.func_name , f)
                   ) fl

  end
