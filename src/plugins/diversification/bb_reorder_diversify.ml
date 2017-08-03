open Visit
open Type
open Pp_print
open Ail_utils

type instr_update = SUB | INSERT

class bb_reorder_diversify =
(* A basic block reoder diversity implementation.
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

      val mutable fb_tbl = Hashtbl.create 40
      val mutable instrs_update = []
      val mutable locs_update = []

      inherit ailVisitor


      method insert_instrs i l =
        instrs_update <- List.rev_append (List.rev instrs_update) [(i, l, INSERT, "")]
        (* instrs_update <- (i, l, INSERT, "")::instrs_update *)

      method sub_instrs i l i' =
        let i_s = pp_print_instr i' in
        instrs_update <- List.rev_append (List.rev instrs_update) [(i, l, SUB, i_s)]
        (* instrs_update <- (i, l, SUB, i_s)::instrs_update *)

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


      method update_instrs_abd instrs =
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
                    loc_addr = l.loc_addr;loc_visible = true;} in
            set_loc i l'


      method add_label_2 i l =
        let l' = get_loc i in
          let l1 = {loc_label = "S_"^(dec_hex l.loc_addr)^"_next : "; loc_addr = l'.loc_addr;
                    loc_visible = true;} in
            (* set_loc i l1 *)
            locs_update <- l1::locs_update


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


      method update_preceding_bb pb b =
        let pb_l = self#bb_instrs pb in
          let last_i = List.nth pb_l (List.length pb_l - 1) in
            let last_loc = get_loc last_i in
        let b_l = self#bb_instrs b in
          let f_i = List.nth b_l 0 in
            let f_loc = get_loc f_i in
            (* print_string "update preceding : "; *)
            (* print_string (dec_hex last_loc.loc_addr); *)
            (* print_string "\n"; *)
        let bn = b.bblock_name in
          let i = DoubleInstr (ControlOP (Jump JMP), Label bn, last_loc, None) in
            self#insert_instrs i f_loc

      method update_succeeding_bb b sb =
        let b_l = self#bb_instrs b
        and sb_l = self#bb_instrs sb in
          let last_i = List.nth b_l (List.length b_l - 1)
          and first_i = List.nth sb_l 0 in
            let loc = get_loc last_i
            and sloc = get_loc first_i in
          let sbn = sb.bblock_name in
          let i = DoubleInstr (ControlOP (Jump JMP), Label sbn, loc, None) in
          (* and first_i' = set_loc first_i *)
                (* {sloc with loc_label = sbn^":\n"^(sloc.loc_label)} in *)
            (* print_string "update succeeding : "; *)
            (* print_string (dec_hex sloc.loc_addr); *)
            (* print_string "\n"; *)
            self#insert_instrs i sloc;
            (* self#sub_instrs first_i' sloc *)

      
      method update_current_bb fb last_loc sb =
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
          | _ -> failwith "failed in update current bb" in
        let rec help2 fl sl last_loc' =
          match (fl,sl) with
          | ([], sh::st) ->
            begin
              let sl = get_loc sh in
                let sh' = set_loc sh {last_loc' with loc_label=sl.loc_label} in
                self#insert_instrs sh' last_loc;
                help2 [] st last_loc'
                (* self#sub_instrs sh l fh *)
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
          | _ -> failwith "failed in update current bb" in
        let fb_l = self#bb_instrs fb
        and sb_l = self#bb_instrs sb in
          let fl = List.length fb_l
          and sl = List.length sb_l in
            if fl >= sl then  
              help1 fb_l sb_l
            else
              help2 fb_l sb_l last_loc  

      (*
      method print_bb_reorder b1 b2 b3 =
        print_string "reorder basic block : ";
        print_string b2.bblock_name;
        print_string " ";
        print_string (dec_hex b2.bblock_begin_loc.loc_addr);
        print_string " ";
        print_string (dec_hex b2.bblock_end_loc.loc_addr);
        print_string "\n"
       *)

      method reorder_bb n1 n2 bl =
        let f_pre_b = List.nth bl n1
        and s_pre_b = List.nth bl n2
        and f_b = List.nth bl (n1+1)
        and s_b = List.nth bl (n2+1)
        and f_suc_b = List.nth bl (n1+2)
        and s_suc_b = List.nth bl (n2+2) in
        (* print_string "=======================\n"; *)
        self#update_preceding_bb f_pre_b f_b;
        self#update_preceding_bb s_pre_b s_b;

        (* print_string "=======================\n"; *)
        self#update_succeeding_bb f_b f_suc_b;
        self#update_succeeding_bb s_b s_suc_b;

        (* print_string "=======================\n"; *)
        self#update_process;
        (* self#print_bb_reorder f_pre_b f_b f_suc_b; *)
        (* self#print_bb_reorder s_pre_b s_b s_suc_b; *)


        (* instrs_update <- List.rev instrs_update; *)



        self#update_current_bb f_b f_suc_b.bblock_begin_loc s_b;
        self#update_current_bb s_b s_suc_b.bblock_begin_loc f_b;

        (* print_string "=======================\n"; *)

 (*            List.iter (
                fun (i, _, _,_) ->
                  print_string ((pp_print_instr i)^" "^(dec_hex (get_loc i).loc_addr)^"\n");
            ) instrs_update;

 *)
        self#update_process;
        (* print_string "=======================\n"; *)

          ()



      method bb_div_reorder =
        let rand_num n max =
          let n' = ref 0 in
          while !n' = n do
              n' := Random.int max;
          done;
          !n'
        in
        let help f bl =
          let len = List.length bl in
          if len > 3 then
            (
              let n1 = Random.int (len-2) in
              let n2 = rand_num n1 (len-2) in
              self#reorder_bb n1 n2 bl;
              ()
            )
          else
            () in
        Hashtbl.iter help fb_tbl;
        print_string "reorder ";
        print_int (Hashtbl.length fb_tbl);
        print_string " basic blocks pairs\n";
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
                               loc_addr = lo.loc_addr;
                               loc_visible = true;} in
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

      method bb_div_process =
        self#bb_div_reorder;
        instrs;


      method visit (il : instr list) : instr list =
      	print_string "start bb reorder \n";
        instrs <- il;
        self#bb_div_process


        method set_fb_tbl (fb : (string, Type.bblock list) Hashtbl.t ) : unit =
          fb_tbl <- fb

        (* method print_hashtb cfi_tbl = *)
          (* Hashtbl.iter (fun k v -> print_string k; print_string "\n"; ()) cfi_tbl *)


    end
