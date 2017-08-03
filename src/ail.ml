open Batteries
open Type
open Ail_parser
open Pp_print
(* open Reassemble *)
open Reassemble_symbol_get
open Cfg
open Cg

open Ail_utils

(* diversify plugins *)
open Func_inline_diversify
open Func_reorder_diversify
open Bb_branchfunc_diversify
open Bb_reorder_diversify
open Bb_split_diversify
open Bb_merge_diversify
open Bb_opaque_diversify
open Bb_flatten_diversify
open Instr_garbage_diversify
open Instr_replace_diversify


class ail =
object (self)
  val mutable funcs : func list = []
  val mutable secs: section list = []
  val mutable intrs: string list = []
  val mutable instrs_list: instr list = []
  val mutable datas: string list = []
  val mutable g_bss: (string*string) list = []

  method sections =
    let filelines = File.lines_of "sections.info"
    and help l =
      let items = Str.split (Str.regexp " +") l in
      let addr = int_of_string ("0x"^(List.nth items 1))
      and size = int_of_string ("0x"^(List.nth items 3))
      and secname = List.nth items 0 in
      secs <- {sec_name=secname; sec_begin_addr=addr;
               sec_size=size}::secs
    in
    Enum.iter help filelines

  method externfuncs =
    let filelines = File.lines_of "externfuncs.info"
    and help l =
      let items = Str.split (Str.regexp " +") l in
      let addr = int_of_string ("0x"^(List.nth items 0))
      and func = List.nth items 1 in
      funcs <- {func_name=func; func_begin_addr=addr; func_end_addr = 0;
                is_lib=true}::funcs
    in
    Enum.iter help filelines

  (* in stripped binary, any user functions' information has been stripped
   *  so slicing function class really does the job *)
  method userfuncs =
    let filelines = File.lines_of "userfuncs.info"
    and help l =
      if String.exists l "-0x" || String.exists l "+0x" then
        ()
      else
        begin
          let items = Str.split (Str.regexp " +") l in
          let addr = int_of_string ("0x"^(List.nth items 0))
          and funname = List.nth items 1 in
          let len = String.length funname in
          let funname' = String.sub funname 1 (len-3) in
          funcs <- {func_name=funname'; func_begin_addr=addr; func_end_addr = 0;
                    is_lib=false}::funcs
        end
    in
    Enum.iter help filelines


  method get_userfuncs =
    List.filter (fun f -> f.is_lib=false) funcs

  method externdatas =
    let filelines = File.lines_of "externdatas.info"
    and help l =
      let data = String.trim l in
      datas <- data::datas
    in
    Enum.iter help filelines

  method global_bss =
    let filelines = File.lines_of "globalbss.info"
    and help l =
      let items = Str.split (Str.regexp " +") l in
      let t = List.nth items 0 in
      let addr = String.sub t 1 ((String.length t)-1) in
      let addr' = String.uppercase addr
      and n = String.trim (List.nth items 1) in
      g_bss <- (addr', n)::g_bss
    in
    Enum.iter help filelines

  method ail_dump =
    (*currently we just dump the extern function info *)
    let check_sym_func f =
      try
        let s = Char.escaped(f.func_name.[0])^Char.escaped(f.func_name.[1]) in
        s <> "__"
      with
      | _ -> false in
    let oc = open_out_gen [Open_append; Open_creat] 0o666 "final.s" in
    (List.filter (fun f -> f.is_lib) funcs
     |> List.filter check_sym_func
     |> List.iter (fun l -> Printf.fprintf oc "extern %s\n" l.func_name));
    close_out oc

  method ehframe_dump =
    Sys.command("cat eh_frame.data >> final.s")

  method excpt_tbl_dump =
    Sys.command("cat gcc_exception_table.data >> final.s")

  method post_process =
    Sys.command("python post_process.py");
    Sys.command("python post_process_lib.py");
    ()
  (*
          self#ehframe_dump;
          self#excpt_tbl_dump;
   *)

  method pre_process =
    let  _ = Sys.command("python pre_process.py") in
    ()


  method get_userfuncs1 funcs =
      List.filter (fun f -> f.is_lib=false) funcs


  method get_current_index () =
   read_file "count.txt" 
   |> (fun c -> List.nth c 0) 
   |> String.strip
   |> int_of_string 


  method get_random_num () =
   Random.int 999 


  method instrProcess_2 f =
    let open Disassemble_process in
    let open Analysis_process in
    let module D = Disam in
    let module A = Analysis in
    let () = self#pre_process in

    let (il, fl, re) = D.disassemble f funcs secs in

	print_endline "3: analysis";

    let (fbl, bbl, cfg_t, cg, il', re) = A.analyze_one il fl re in

    let u_funcs = self#get_userfuncs1 fl in

     (* diversify plugin define *)
    let func_inline_div = new func_inline_diversify in
    let func_rod_div = new func_reorder_diversify in

    let bb_bfn_div = new bb_branchfunc_diversify in
    let bb_fln_div = new bb_flatten_diversify in
    let bb_opq_div = new bb_opaque_diversify in
    let bb_spt_div = new bb_split_diversify in
    let bb_meg_div = new bb_merge_diversify in
    let bb_rod_div = new bb_reorder_diversify in

    let ins_gar_div = new instr_garbage_diversify in
    let ins_rpl_div = new instr_replace_diversify in


     (* diversify plugin init *)
    func_rod_div#set_funclist u_funcs;
    func_inline_div#set_funclist u_funcs;

    bb_bfn_div#set_funclist u_funcs;
    bb_fln_div#set_cfg_tbl cfg_t;
    bb_fln_div#set_fb_tbl fbl;
    bb_fln_div#set_funclist u_funcs;
    bb_opq_div#set_fb_tbl fbl;
    bb_spt_div#set_fb_tbl fbl;
    bb_meg_div#set_fb_tbl fbl;
    bb_meg_div#set_cfg_tbl cfg_t;
    bb_rod_div#set_fb_tbl fbl;

    ins_gar_div#set_fb_tbl fbl;


     (* diversify plugin process *)

     
     (* 1: basic block reorder diversify *)
     (* let il' = bb_rod_div#visit il' in *)
     (* 2: basic block split diversify *)
     (* let il' = bb_spt_div#visit il' in *)
     (* 3: instruction garbage insertion diversify *)
     (* let il' = ins_gar_div#visit il' in *)
     (* 4: instruction replace diversify *)
     (* let il' = ins_rpl_div#visit il' in *)
     (* 5: function reorder diversify *)
     (* let il' = func_rod_div#visit il' in *)
     (* 6: basic block opaque predicate diversify *)
     (* let il' = bb_opq_div#visit il' in *)
     (* 7: function inline diversify *)
     (* let il' = func_inline_div#visit  il' in *)
     (* 8: basic block merge diversify *)
     (* let il' = bb_meg_div#visit il' in *)
     (* 9: basic block flatten diversify *)
     (* let il' = bb_fln_div#visit il' in *)
     (* 10: control flow branch function diversify *)
     (* let il' = bb_bfn_div#visit il' in *)

    print_endline "5: post processing";
    A.post_analyze il' re;

    self#post_process


end
