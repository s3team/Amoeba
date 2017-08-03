open Batteries

open Visit
open Type
open Pp_print
open Ail_utils

type instr_update = SUB | INSERT

class func_inline_diversify =
  (* function inline div implementation.
   *
   *  
   *
   *
   *
   *)

  let dec_hex (s:int) : string =
    "0x"^(Printf.sprintf "%X" s) in
  (* let cg_tbl = Hashtbl.create 500
    and cfi_tbl = Hashtbl.create 500  in
   *)


  let size_Threshold = 500 in

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
                 (* print_string "\n"; *)
                 (* print_string (dec_hex loc1.loc_addr); *)
                 match ty with
                 | SUB ->
                    begin
                      let h_s = pp_print_instr h in
                      if i_s = h_s then
                        begin
                          (* print_string (" sub "^(pp_print_instr i)^"\n"); *)
                          (help t_u (i::t))
                        end
                      else
                        h::(help l_u t)
                    end
                 | INSERT ->
                    begin
                      (* let iloc' = get_loc i in *)
                      (* print_string (" insert "^(pp_print_instr i)^" "^(dec_hex iloc'.loc_addr)^"\n"); *)
                      i::(help t_u (h::t))
                    end
               end
             else
               h::(help l_u t)
           end
        | ([], l') -> l'
        | (h::t, []) ->
           begin
             (*let (_,l,_, _) = h in *)
             (* print_string "\n"; *)
             (* print_string (dec_hex l.loc_addr); *)
             (* print_string "\n"; *)
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
      let l1 = {loc_label = "S_"^(dec_hex l.loc_addr)^"_next : ";
                loc_addr = l'.loc_addr; loc_visible=true;} in
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


    method print_func_inline f l =
      print_endline "inline function : ";
      print_endline f.func_name;
      print_endline " in addr : ";
      print_endline (dec_hex l.loc_addr)


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


    method target_func_scan =
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
      let scan acc f =
        let s = f.func_end_addr - f.func_begin_addr in
        if s < size_Threshold && s <> 13 then f::acc
        else acc in
      let tfl = List.fold_left scan [] func_list in
      let flen = List.length tfl in
      print_string "function inline : ";
      print_int flen;
      print_string " candidate\n";
      
      if flen > 0 then
        begin
	(*
          let n' = ref 0 in
          let n = ref 0 in
          while !n' = 0 do
	*)
            let n = Random.int flen in
	    if is_main n then
	        None
            else
		begin
                let tf = (List.nth tfl n) in
                let n' = List.length (self#caller_collect tf.func_name) in
		if n' = 0 then
		begin
		    print_string "found zero caller function\n";
		    None
		end
		else
                    Some tf
		end
           (*
	    done;
            let tf = (List.nth tfl !n) in
	   *)
        end
      else
        None

    method caller_collect fn =
      let is_call op =
        match op with
        | ControlOP c ->
           begin
             match c with
             | CALL -> true
             | _ -> false
           end
        | _ -> false in
      let help acc i =
        match i with
        | DoubleInstr (p, e, _, _) when (is_call p) ->
           let es = p_exp e in
           if String.exists es fn then
             i::acc
           else acc
        | _ -> acc in
      List.fold_left help [] instrs

    (*
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

    method transform_caller cl =
      (* let it crashes if not *)
      let help ci =
        let DoubleInstr (_,e,l, _) = ci in
        self#update_call ci e l
      in
      List.iter help cl;
      cl

    (*
     * call $func
     *    ==>
     * push $next_instr
     * jmp $some_function
     * $next_instr:
     *   ...
     *)
    method update_call i e l =
      let help i e l =
        let jmp_label = "S_"^(dec_hex l.loc_addr)^"_next_inline" in
        let l1 = {l with loc_label = ""} in
        let i2 =
          DoubleInstr (StackOP PUSH, Label ("$"^jmp_label), l, None)
        and i3 =
          DoubleInstr (ControlOP (Jump JMP), e, l1, None)
        and i1 =
          SingleInstr (CommonOP (Other NOP), {l with loc_label = jmp_label^": "}, None) in
        self#sub_instrs i1 l i;
        self#insert_instrs i2 l;
        self#insert_instrs i3 l  in
      match e with
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

    method symbol_collect il =
      let aux acc i =
        let l = get_loc i in
        let label = l.loc_label in
        if String.exists label ":" then label::acc
        else acc in
      List.fold_left aux [] il

    method symbol_dump il =
      Sys.command("rm inline_symbols.txt");
      let sl = self#symbol_collect il in
      let oc = open_out_gen [Open_append; Open_creat] 0o666 "inline_symbols.txt" in
      List.iter (fun l -> Printf.fprintf oc "%s\n" l) (sl);
      close_out oc


    (* this function will insert target function into *)
    method inline tf cl =
      let tf_l = self#func_instrs tf in
      List.iter (
          fun i ->
          (
            let l = get_loc i in
            self#print_func_inline tf l;
            List.iter (fun i -> self#insert_instrs i l) tf_l
          )
        ) cl;

      (* provide symbols for inline_update.py *)

      self#symbol_dump tf_l;

      self#update_process


    method func_inline_process =
      let rand_num n max =
        let n' = ref 0 in
        while !n' = n do
            n' := Random.int max;
        done;
        !n'
      in
      match self#target_func_scan with
      | None -> instrs
      | Some tf ->
         begin
           let l = self#caller_collect tf.func_name in
	   if List.length l > 40 then
	     begin
               print_string "too much callers\n";
               instrs
	     end
           else if List.length l <> 0 then
             begin
               let tl = self#transform_caller l in
               self#inline tf tl;
               instrs
             end
           else
             begin
             print_string "caller equals to zero\n";
             instrs
             end
         end


    method visit (il : instr list) : instr list =
	print_string "func inline start\n";
      instrs <- il;
      
      if List.length func_list < 5 then instrs
      else self#func_inline_process


    method set_funclist (fl : func list) : unit =
      func_list <- fl

  end
