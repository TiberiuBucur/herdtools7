(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2024-present Institut National de Recherche en Informatique et *)
(* en Automatique and the authors. All rights reserved.                     *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

let memloc loc =
  Printf.sprintf "\\memloc{%s}" loc

let reg reg =
  Printf.sprintf "\\reg{%s}" reg

let mem_read loc reg =
  Printf.sprintf "\\ExpMREof{\\memlocAddrBy{%s}{%s}}" loc reg

let mem_write loc reg =
  Printf.sprintf "\\ExpMWEof{\\memlocAddrBy{%s}{%s}}" loc reg

let tag_read loc reg =
  Printf.sprintf "\\ImpTagMREof{\\taglocOf{%s}{\\memlocAddrBy{%s}{%s}}}" loc loc reg

let tag_write loc reg =
  Printf.sprintf "\\ImpTagMWEof{\\taglocOf{%s}{\\memlocAddrBy{%s}{%s}}}" loc loc reg

let pte_read loc reg =
  Printf.sprintf "\\ExpMREof{\\PTEof{\\memlocAddrBy{%s}{%s}}}" loc reg

let pte_write loc reg =
  Printf.sprintf "\\ExpMWEof{\\PTEof{\\memlocAddrBy{%s}{%s}}}" loc reg

let pa_read loc reg =
  Printf.sprintf "\\ExpMREof{\\PAof{\\memlocAddrBy{%s}{%s}}}" loc reg

let pa_write loc reg =
  Printf.sprintf "\\ExpMWEof{\\PAof{\\memlocAddrBy{%s}{%s}}}" loc reg

let reg_read reg =
  Printf.sprintf "\\RREof{%s}" reg

let reg_write reg =
  Printf.sprintf "\\RWEof{%s}" reg

let mte_cond loc reg =
  Printf.sprintf "\\iseqCheck{\\allocTagOf{%s}}{\\logAddrTagIn{%s}}" loc reg

let pte_cond loc reg pred =
  Printf.sprintf "\\PTECheck{%s}{%s}{%s}" loc reg pred

let instr_cond cond =
  Printf.sprintf "\\cond{%s}" cond

let eq_contents lhs rhs =
  Printf.sprintf "\\eqContentsCheck{%s}{%s}" lhs rhs

let neq_contents lhs rhs =
  Printf.sprintf "\\neqContentsCheck{%s}{%s}" lhs rhs

let branching cond =
  Printf.sprintf "\\IntrBranching{%s}" cond

let bcc_branching = "\\BccBranching{}"

let fault name =
  Printf.sprintf "\\genericFault{%s}" name

let exc_entry name =
  Printf.sprintf "\\genericExcEntry{%s}" name

let iico_data e1 e2 =
  Printf.sprintf "\\iicodata{%s}{%s}" e1 e2

let iico_ctrl e1 e2 =
  Printf.sprintf "\\iicoctrl{%s}{%s}" e1 e2

let iico_order e1 e2 =
  Printf.sprintf "\\iicoorder{%s}{%s}" e1 e2

let edges = StringMap.empty |>
  StringMap.add "iico_data" iico_data |>
  StringMap.add "iico_ctrl" iico_ctrl |>
  StringMap.add "iico_order" iico_order
