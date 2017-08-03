open Batteries

open Visit
open Type
open Pp_print
open Ail_utils

type instr_update = SUB | INSERT

class bb_merge_diversify =
  (* A basic block merge diversity implementation.
   *
   *
   *
   *)
  let dec_hex (s:int) : string =
    "0x"^(Printf.sprintf "%X" s) in

  object(self)

    val mutable fb_tbl = Hashtbl.create 40
    (* how to choose the size ? *)
    val mutable cfg_t = []
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

    method update_first_bb b =
      let bil = self#bb_instrs b in
      let blen = List.length bil in
      let i = List.nth bil (blen - 1) in
      let iloc = get_loc i in
      let i' = SingleInstr (CommonOP (Other NOP), iloc,None) in
      self#sub_instrs i' iloc i;
      self#update_process;
      iloc

    method update_second_bb iloc b =
      let bil = self#bb_instrs b in
      let bn = b.bblock_name in
      let blen = List.length bil in
      let i = List.nth bil (blen - 1) in
      let last_loc = get_loc i in

      let i1 =
        DoubleInstr (ControlOP (Jump JMP),
                     Label (bn^"_merge"), {last_loc with loc_label = ""}, None)
      and i2 =
        SingleInstr (CommonOP (Other NOP), {last_loc with loc_label = (bn^"_merge:")}, None) in
      List.iter (
          fun i ->
          let cloc = get_loc i in
          let inop =
            SingleInstr (CommonOP (Other NOP), {cloc with loc_label = ""}, None) in
          self#sub_instrs inop cloc i
        ) bil;
      List.iter (
          fun i ->
          self#insert_instrs i iloc
        ) bil;
      self#insert_instrs i1 iloc;
      self#insert_instrs i2 last_loc;
      self#update_process;


    method print_bb_merge b1 b2 =
      print_string "merge basic block : ";
      print_string b1.bblock_name;
      print_string " ";
      print_string b2.bblock_name;
      print_string "\n"

    method merge_bb p =
      let (f,s,d) = p in
      let bbl = Hashtbl.find fb_tbl f in
      let tl =
        List.fold_left ( (* let it crash it not matched *)
            fun acc b ->
            if b.bblock_name = s then b::acc
            else if b.bblock_name = d then
	        acc@[b]
            else acc
          ) [] bbl in
	if List.length tl = 2 then
	begin
	let sb::db::[] = tl in
      	self#print_bb_merge sb db;
      	let l = self#update_first_bb sb in
      	self#update_second_bb l db;
      	()
	end
	else
	begin
	    print_string "we found a inter-procedural jmp\n";
	    print_string (List.nth tl 0).bblock_name;
	    print_string " ";
	    print_string (List.nth tl 0).bf_name;
	    print_string " prbabaly caused by bb_flattern\n";
	    ()
	end

    (*
     *)
    method bb_div_merge =
      let rand_num n max =
        let n' = ref 0 in
        while !n' = n do
          n' := Random.int max;
        done;
        !n'
      in
      let help bbl =
        let len = List.length bbl in
        if len > 0 then
          (
          (* let n = rand_num (-1) (len-1) in *)
           (*  let n = (Random.int 9999999) mod len in *)
            let n = Random.int len in
            print_string "random number : ";
            print_int n;
            print_string "\n";
            let p = List.nth bbl 0 in
            self#merge_bb p;
            ()
          )
        else
          () in
      let mgb_pairl = self#mergeable_bb cfg_t in
      print_string "we have ";
      print_int (List.length mgb_pairl);
      print_string " candidates to merge! \n";
      help mgb_pairl

    (*

     *)
    method mergeable_bb cfg_t =
      List.fold_left (
          fun acc1 (f, v) ->
          let ic = List.exists (fun t ->
                               match t with
                               | (_, (_, None)) -> false
                               | (_, (_, Some(s))) when s = "T" -> true
                               | (_, (_, Some(s))) when s = "INTER" -> true
                               | (_, (_, Some(s))) when s = "RET" -> false
                               | (s, (_, Some(d))) -> false
                    ) v in
          if ic = true then acc1
          else
          begin
          let t = List.fold_left (
                      fun acc t ->
                      match t with
                      | (_, (_, None)) -> acc
                      | (_, (_, Some(s))) when s = "T" -> acc
                      | (_, (_, Some(s))) when s = "INTER" -> acc
                      | (_, (_, Some(s))) when s = "RET" -> acc
                      | (s, (_, Some(d))) -> (s,d)::acc
                    ) [] v in
          let sl = List.map (fun (s,_) -> s) t in
          let dl = List.map (fun (_,d) -> d) t in
          let sl' = remove_over_once sl in
          let dl' = remove_over_once dl in
          List.fold_left (
              fun acc s ->
              match List.assoc s v with
              |  (_, Some(d)) when List.mem d dl' ->
                 begin
                   assert(String.exists s "BB_");
                   assert(String.exists d "BB_");
                   (f,s,d)::acc
                 end
              | _ -> acc
            ) acc1 sl';
        end
        ) [] cfg_t


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
      self#bb_div_merge;
      instrs;


    method visit (il : instr list) : instr list =
      print_string "start bb merge \n";
      instrs <- il;
      self#bb_div_process


    method set_fb_tbl (fb : (string, Type.bblock list) Hashtbl.t ) : unit =
      fb_tbl <- fb

    method set_cfg_tbl (tb : (string * (string * (Type.control * string option)
                                       ) list) list) : unit =
      cfg_t <- tb
  end
