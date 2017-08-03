open Batteries
open Visit
open Type
open Pp_print
open Ail_utils

type instr_update = SUB | INSERT

class func_reorder_diversify =
  (* function reoder div implementation.
   *
   *
   *
   * *)
  let dec_hex (s:int) : string =
    "0x"^(Printf.sprintf "%X" s) in
  (* let cg_tbl = Hashtbl.create 500
    and cfi_tbl = Hashtbl.create 500  in
   *)

  object(self)

    val mutable func_list = []
    val mutable instrs_update = []
    val mutable locs_update = []

    inherit ailVisitor

    method insert_instrs i l =
      instrs_update <- instrs_update@[(i, l, INSERT, "")]
    (* instrs_update <- (i, l, INSERT, "")::instrs_update *)

    method sub_instrs i l i' =
      let i_s = pp_print_instr i' in
      instrs_update <- instrs_update@[(i, l, SUB, i_s)]
    (* instrs_update <- (i, l, SUB, i_s)::instrs_update *)

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




    method add_label i =
      let l = get_loc i in
      let l' = {loc_label = l.loc_label^(dec_hex l.loc_addr);
                loc_addr = l.loc_addr; loc_visible = true;
               } in
      set_loc i l'


    method add_label_2 i l =
      let l' = get_loc i in
      let l1 = {loc_label = "S_"^(dec_hex l.loc_addr)^"_next : "; loc_addr = l'.loc_addr;
                loc_visible = true;} in
      (* set_loc i l1 *)
      locs_update <- l1::locs_update

    
    method func_instrs f =
      let baddr = f.func_begin_addr
      and eaddr = f.func_end_addr in
      let rec help il acc =
        match il with
        | h::t ->
           begin
             let loc = get_loc h in
             if loc.loc_addr >= baddr &&
                  loc.loc_addr < eaddr then
               help t (h::acc)
             else help t acc
           end
        | [] -> List.rev acc in
      help instrs []


    method update_preceding_func pf f =
      let pf_l = self#func_instrs pf in
      let last_i = List.nth pf_l (List.length pf_l - 1) in
      let last_loc = get_loc last_i in
      let f_l = self#func_instrs f in
      let f_i = List.nth f_l 0 in
      let f_loc = get_loc f_i in
      (* print_string "update preceding : "; *)
      (* print_string (dec_hex last_loc.loc_addr); *)
      (* print_string "\n"; *)
      let fn = f.func_name in
      let i = DoubleInstr (ControlOP (Jump JMP), Label fn, last_loc, None) in
      self#insert_instrs i f_loc

    method update_succeeding_func f sf =
      let f_l = self#func_instrs f
      and sf_l = self#func_instrs sf in
      let last_i = List.nth f_l (List.length f_l - 1)
      and first_i = List.nth sf_l 0 in
      let loc = get_loc last_i
      and sloc = get_loc first_i in
      let sfn = sf.func_name in
      let i = DoubleInstr (ControlOP (Jump JMP), Label sfn, loc, None) in
      (* and first_i' = set_loc first_i *)
      (* {sloc with loc_label = sbn^":\n"^(sloc.loc_label)} in *)
      (* print_string "update succeeding : "; *)
      (* print_string (dec_hex sloc.loc_addr); *)
      (* print_string "\n"; *)
      self#insert_instrs i sloc;
    (* self#sub_instrs first_i' sloc *)

    
    method update_current_func ff last_addr sf =
      let rec help1 fl sl =
        match (fl,sl) with
        | (fh::ft, []) ->
           begin
             let floc = get_loc fh in
             let i = SingleInstr (CommonOP (Other NOP), {floc with loc_label = ""}, None) in
             self#sub_instrs i floc fh;
             help1 ft []
           end
        | (fh::ft, sh::st) ->
           begin
             let floc = get_loc fh
             and sloc = get_loc sh in
             let sh' = set_loc sh {floc with loc_label=sloc.loc_label} in
             self#sub_instrs sh' floc fh;
             (* self#sub_instrs sh floc fh; *)
             help1 ft st
           end
        | ([], []) -> ()
        | _ -> failwith "failed in update current function" in
      let rec help2 fl sl last_loc' =
        match (fl,sl) with
        | ([], sh::st) ->
           begin
             let sl = get_loc sh in
             let sh' = set_loc sh {last_loc' with loc_label=sl.loc_label} in
             self#insert_instrs sh' {loc_addr=last_addr; loc_label=""; loc_visible=true;};
             help2 [] st last_loc'
           end
        | (h::[], sh::st) ->
           begin
             let l = get_loc h
             and sl = get_loc sh in
             let sh' = set_loc sh {l with loc_label=sl.loc_label} in
             self#sub_instrs sh' l h;
             help2 [] st l
           end
        | (fh::ft, sh::st) ->
           begin
             let fl = get_loc fh
             and sl = get_loc sh in
             let sh' = set_loc sh {fl with loc_label=sl.loc_label} in
             (* let sh' = set_loc sh floc in *)
             self#sub_instrs sh' fl fh;
             (* self#sub_instrs sh floc fh; *)
             help2 ft st fl
           end
        | ([], []) -> ()
        | _ -> failwith "failed in update current func" in
      let ff_l = self#func_instrs ff
      and sf_l = self#func_instrs sf in
      let fl = List.length ff_l
      and sl = List.length sf_l in
      if fl >= sl then  
        help1 ff_l sf_l
      else
        help2 ff_l sf_l {loc_addr=last_addr; loc_label=""; loc_visible=true;}
    

    method print_func_reorder f1 f2 =
      print_string "reorder function : ";
      print_string f1.func_name;
      print_string " ";
      print_string (dec_hex f1.func_begin_addr);
      print_string " ";
      print_string (dec_hex f1.func_end_addr);
      print_string " ";
      print_string f2.func_name;
      print_string " ";
      print_string (dec_hex f2.func_begin_addr);
      print_string " ";
      print_string (dec_hex f2.func_end_addr);
      print_string "\n"

    method reorder_funcs n1 n2 func_list =
      let f_pre_f = List.nth func_list n1
      and s_pre_f = List.nth func_list n2
      and f_f = List.nth func_list (n1+1)
      and s_f = List.nth func_list (n2+1)
      and f_suc_f = List.nth func_list (n1+2)
      and s_suc_f = List.nth func_list (n2+2) in
      self#update_preceding_func f_pre_f f_f;
      self#update_preceding_func s_pre_f s_f;

      self#update_succeeding_func f_f f_suc_f;
      self#update_succeeding_func s_f s_suc_f;

      self#update_process;

      self#print_func_reorder s_f f_f;
      self#update_current_func f_f f_suc_f.func_begin_addr s_f;
      self#update_current_func s_f s_suc_f.func_begin_addr f_f;

      self#update_process;

      ()


    (*
     *)

    method func_div_reorder =
      let is_main n =
	let t = List.nth func_list n in
   	let c = read_file "main.info" in
   	let c' = List.nth c 0 in
   	let c1 = String.strip c' in
	let c1 = String.sub c1 2 (String.length c1 - 2) in
   	let cn = int_of_string c1 in
	if cn = t.func_begin_addr || cn = t.func_end_addr then
	    begin
	    print_string "ignore this pass\n";
		print_string (dec_hex t.func_begin_addr);
		print_string (dec_hex t.func_end_addr);
	    true
	    end
        else false in
      let rand_num n max =
        let n' = ref 0 in
        while !n' = n do
          n' := Random.int max;
        done;
        !n'
      in
      let len = List.length func_list in
      print_string "function reorder : ";
      print_int len;
      print_string " candidates\n";
      if len > 5 then
        (
          let n1 = Random.int (len-4) in
          (*let n2 = rand_num n1 (len-2) in*)
          let n2 = n1 + 1  in
	  if is_main n1 || is_main n2 || is_main (n1+1) || is_main (n2+1) || is_main (n1+2) || is_main (n2+2) then
	    ()
	  else
          self#reorder_funcs n1 n2 func_list;
          ()
        )
      else
        ()


    method update_locs instrs =
      locs_update <- List.rev locs_update;
      let rec help il ll acc =
        match (il, ll) with
        | (ih::it, lh::lt) ->
           begin
             let lo = get_loc ih in
             if lo.loc_addr = lh.loc_addr then
               begin
                 (* print_string lh.loc_label; *)
                 (* print_string "\n"; *)
                 let ih' = set_loc ih
                                   {loc_label = lo.loc_label^"\n"^lh.loc_label;
                                    loc_addr = lo.loc_addr; loc_visible=true;} in
                 help it lt (ih'::acc)
               end
             else
               (
                 (* print_string (dec_hex lh.loc_addr); *)
                 (* print_string "\n"; *)
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

    method func_div_process =
      self#func_div_reorder;
      instrs;


    method visit (il : instr list) : instr list =
	print_string "func reorder start\n";
      instrs <- il;
      self#func_div_process


    method set_funclist (fl : func list) : unit =
	print_string "func length\n";
	print_int (List.length fl);
	print_string "\n";
      func_list <- fl

  end
