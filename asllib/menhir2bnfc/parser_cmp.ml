(******************************************************************************)
(*                                ASLRef                                      *)
(******************************************************************************)
(*
 * SPDX-FileCopyrightText: Copyright 2022-2023 Arm Limited and/or its affiliates <open-source-office@arm.com>
 * SPDX-License-Identifier: BSD-3-Clause
 *)
(******************************************************************************)
(* Disclaimer:                                                                *)
(* This material covers both ASLv0 (viz, the existing ASL pseudocode language *)
(* which appears in the Arm Architecture Reference Manual) and ASLv1, a new,  *)
(* experimental, and as yet unreleased version of ASL.                        *)
(* This material is work in progress, more precisely at pre-Alpha quality as  *)
(* per Arm’s quality standards.                                               *)
(* In particular, this means that it would be premature to base any           *)
(* production tool development on this material.                              *)
(* However, any feedback, question, query and feature request would be most   *)
(* welcome; those can be sent to Arm’s Architecture Formal Team Lead          *)
(* Jade Alglave <jade.alglave@arm.com>, or by raising issues or PRs to the    *)
(* herdtools7 github repository.                                              *)
(******************************************************************************)

(*
   A script to compare a command line parser tool to the aslref latest ASL parser
*)

type args = { files : string list; output_file : string; quiet : bool }
type cmp_res = Pass | Fail of { aslref : bool; bnfc : bool }

let string_of_cmp_res cmp_res =
  match cmp_res with
  | Pass -> "PASS"
  | Fail { aslref; bnfc } ->
      Printf.sprintf "FAIL - aslref %s | bnfc %s" (string_of_bool aslref)
        (string_of_bool bnfc)

let parse_args () =
  let files = ref [] in
  let output_file = ref "" in
  let quiet = ref false in
  let speclist =
    [
      ( "-o",
        Arg.Set_string output_file,
        " The output file to write the results to." );
      ("-q", Arg.Set quiet, " Only print back mismatched cases.");
    ]
  in
  let prog =
    if Array.length Sys.argv > 0 then Filename.basename Sys.argv.(0)
    else "parser_cmp"
  in
  let anon_fun f = files := f :: !files in
  let usage_msg =
    Printf.sprintf
      "A tool to compare a parser binary to AslRef against a set of tests.\n\n\
       USAGE:\n\
       \t%s [TARGETS]\n"
      prog
  in
  let () = Arg.parse speclist anon_fun usage_msg in
  let ensure_exists s =
    if Sys.file_exists s then ()
    else
      let () = Printf.printf "%s\n" (Sys.getcwd ()) in
      let () = Printf.eprintf "%s cannot find file %S\n%!" prog s in
      exit 1
  in
  let files =
    List.iter ensure_exists !files;
    !files
  in
  let output_file = !output_file in
  let quiet = !quiet in
  { files; output_file; quiet }

let compare_parsers file =
  let parsed _ = true in
  let aslref =
    try Asllib.Builder.from_file `ASLv1 file |> parsed with _ -> false
  in
  let bnfc =
    let open Bnfc_parser in
    let chan = open_in file in
    let lexbuf = Lexing.from_channel chan in
    let res =
      try ParGrammar.pSpec LexGrammar.token lexbuf |> parsed with _ -> false
    in
    close_in chan;
    res
  in
  if Bool.equal aslref bnfc then Pass else Fail { aslref; bnfc }

(**
   Taken from https://gist.github.com/lindig/be55f453026c65e761f4e7012f8ab9b5 (ty Chris)
*)
let dir_contents files =
  let rec loop result = function
    | f :: fs when Sys.is_directory f ->
        Sys.readdir f |> Array.to_list
        |> List.map (Filename.concat f)
        |> List.append fs |> loop result
    | f :: fs -> loop (f :: result) fs
    | [] -> result
  in
  loop [] files

let collect_asl files =
  dir_contents files
  |> List.filter (fun f -> String.equal (Filename.extension f) ".asl")

let compare_all args =
  let files = collect_asl args.files in
  let results =
    let res = List.map (fun f -> (f, compare_parsers f)) files in
    if args.quiet then List.filter (function _, Pass -> false | _ -> true) res
    else res
  in
  let output =
    List.map
      (fun (f, res) -> Printf.sprintf "%s: %s" (string_of_cmp_res res) f)
      results
    |> List.sort String.compare |> String.concat "\n"
  in
  if String.equal args.output_file "" then Printf.printf "%s\n" output
  else
    let chan = open_out args.output_file in
    Printf.fprintf chan "%s\n" output;
    close_out chan

let () =
  let args = parse_args () in
  compare_all args
