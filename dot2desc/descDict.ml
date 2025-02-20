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

let memloc_addr_by loc reg =
  Printf.sprintf "\\memlocAddrBy{%s}{%s}" loc reg

let tagloc_of loc reg =
  Printf.sprintf "\\taglocOf{%s}{%s}" loc (memloc_addr_by loc reg)

let pte_of loc reg =
  Printf.sprintf "\\PTEof{%s}" (memloc_addr_by loc reg)

let pa_of loc reg =
  Printf.sprintf "\\PAof{%s}" (memloc_addr_by loc reg)

let tlb_of loc reg =
  Printf.sprintf "\\TLBof{%s}" (memloc_addr_by loc reg)

let reg reg =
  Printf.sprintf "\\reg{%s}" reg

let reg_pair reg1 reg2 =
  Printf.sprintf "\\regPair{%s}{%s}" reg1 reg2

let mre_of arg is_explicit =
  if is_explicit then
    Printf.sprintf "\\ExpMREof{%s}" arg
  else
    Printf.sprintf "\\ImpMREof{%s}" arg

let mwe_of arg is_explicit =
  if is_explicit then
    Printf.sprintf "\\ExpMWEof{%s}" arg
  else
    Printf.sprintf "\\ImpMWEof{%s}" arg

let mem_read loc reg is_explicit =
  let arg = memloc_addr_by loc reg in
  mre_of arg is_explicit

let mem_write loc reg is_explicit =
  let arg = memloc_addr_by loc reg in
  mwe_of arg is_explicit

let tag_read loc reg is_explicit =
  if is_explicit then
    Printf.sprintf "\\ExpTagMREof{%s}" (tagloc_of loc reg)
  else
    Printf.sprintf "\\ImpTagMREof{%s}" (tagloc_of loc reg)

let tag_write loc reg is_explicit =
  if is_explicit then
    Printf.sprintf "\\ExpTagMWEof{%s}" (tagloc_of loc reg)
  else  
    Printf.sprintf "\\ImpTagMWEof{%s}" (tagloc_of loc reg)

let pte_read loc reg is_explicit =
  let arg = pte_of loc reg in
  mre_of arg is_explicit

let pte_write loc reg is_explicit =
  let arg = pte_of loc reg in
  mwe_of arg is_explicit

let pa_read loc reg is_explicit =
  let arg = pa_of loc reg in
  mre_of arg is_explicit

let pa_write loc reg is_explicit =
  let arg = pa_of loc reg in
  mwe_of arg is_explicit

let ifetch label instr =
  Printf.sprintf "\\IFetch{%s}{%s}" label instr

let tlbi typ loc =
  Printf.sprintf "\\TLBIof{%s}{%s}" typ loc

let generic_tlbi typ =
  Printf.sprintf "\\genericTLBI{%s}" typ

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

let any_active r =
  Printf.sprintf "\\AnyActive{%s}" (reg r)

let active_elem r idx =
  Printf.sprintf "\\ActiveElem{%s}{%s}" (reg r) idx

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

let empty = "\\Empty{}"

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
