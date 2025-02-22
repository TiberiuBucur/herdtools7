record = "AArch64 VMSA"

cats = [
    "cats/aarch64.cat",
    ]

cfgs = [
    "cfgs/new-web.cfg",
]

illustrative_tests = [
    "tests/2+2WNExpExp+NExpExp+DMBST+DMBST+SHOW.litmus",
    "tests/2+2WNExpExp+NExpExp+DMBST+DMBST.litmus",
    "tests/2+2WNExpExp+NExpExp+SHOW.litmus",
    "tests/2+2WNExpExp+NExpExp.litmus",
    "tests/Artem2+TLBIx-HDy+dsb.ish.litmus",
    "tests/Artem2+TLBIx-TLBIy+dmb2.litmus",
    "tests/Artem2+TLBIx-UCy+dsb.ish.litmus",
    "tests/Artem3+HDx-TLBIy+dmb.st+dmb.ld.litmus",
    "tests/Artem3+HDx-TLBIy+dsb.st+dmb.ld.litmus",
    "tests/Artem3+TLBIVMALL+dmb.sy+dmb.ld.litmus",
    "tests/Artem3+TLBIx-TLBIy+dmb.sy+dmb.ld.litmus",
    "tests/Artem3+TLBIy-TLBIx+dmb.sy+dmb.ld.litmus",
    "tests/Artem3+UCx-TLBIy+dsb.ish-isb+dmb.ld.litmus",
    "tests/CAS-AF.litmus",
    "tests/CASAL+FAIL+FH.litmus",
    "tests/CASAL+FAIL2+FH.litmus",
    "tests/CoWR.T.inv+po-addr.litmus",
    "tests/D15347-2+2W+DMBST+DSB-ISB.litmus",
    "tests/D15347-2+2WExpExp+DMBST+DSB-ISB.litmus",
    "tests/D15347-2+2WExpExp+DMBST+DSB-ISB2.litmus",
    "tests/D15347-2+2WExpNExp+DMBST+DSB-ISB.litmus",
    "tests/D15347-M-load-DMBST+DMBLD.litmus",
    "tests/D15347-M-load-DSB+DSB-ISB.litmus",
    "tests/D15347-M-load-shoot+DMB.LD+VMALL.litmus",
    "tests/D15347-M-load-shoot+DMB.LD.litmus",
    "tests/D15347-M-load-shoot+acq-po+VMALL.litmus",
    "tests/D15347-M-load-shoot+acq-po.litmus",
    "tests/D15347-M-load-shoot+addr.litmus",
    "tests/D15347-M-load-shoot+ctrl.litmus",
    "tests/D15347-M-load-shoot+ctrlisb.litmus",
    "tests/D15347-M-load-shoot+po+AF.litmus",
    "tests/D15347-M-load-shoot+po.litmus",
    "tests/D15347-M-load-shoot-noscope+DMB.LD.litmus",
    "tests/D15347-M-load.litmus",
    "tests/D15347-M-store-DMBST+DMBLD.litmus",
    "tests/D15347-M-store-DSB+DMBLD.litmus",
    "tests/D15347-M-store-DSB+DSB-ISB.litmus",
    "tests/D15347-M-store-DSB+ctrl.litmus",
    "tests/D15347-M-store-shoot+DMB.LD+VMALL.litmus",
    "tests/D15347-M-store-shoot+DMB.LD.litmus",
    "tests/D15347-M-store-shoot+DMB.ST+VMALL.litmus",
    "tests/D15347-M-store-shoot+DMB.ST.litmus",
    "tests/D15347-M-store-shoot+ctrl.litmus",
    "tests/D15347-M-store.litmus",
    "tests/D15347-MP+DMBST+DSB-ISB2.litmus",
    "tests/D15347-MP+shoot+DSB+HD.litmus",
    "tests/D15347-MP+shoot+DSB-ISB+VMALL.litmus",
    "tests/D15347-MP+shoot+DSB-ISB-RO.litmus",
    "tests/D15347-MP+shoot+DSB-ISB.litmus",
    "tests/D15347-R-DMBST+DMB.litmus",
    "tests/D15347-R-DMBST+DSB-ISB.litmus",
    "tests/D15347-R-DSB+DSB-ISB.litmus",
    "tests/D15347-S+DMBST+DSB-ISB2.litmus",
    "tests/D15347-SB-DSB+DSB-ISB.litmus",
    "tests/D15347-load-DMB.litmus",
    "tests/D15347-load-DSB-ISB.litmus",
    "tests/D15347-load-DSB-ISB2.litmus",
    "tests/D15347-load-DSB-ISB3.litmus",
    "tests/D15347-load-DSB-ISB4.litmus",
    "tests/D15347-load-DSB-TLBI-DSB2.litmus",
    "tests/D15347-load-DSB.litmus",
    "tests/D15347-load-invalid.litmus",
    "tests/D15347-load-rel-acq.litmus",
    "tests/D15347-load-shoot+VMALL.litmus",
    "tests/D15347-load-shoot.litmus",
    "tests/D15347-load-valid.litmus",
    "tests/D15347-load.litmus",
    "tests/D15347-store-DMB.litmus",
    "tests/D15347-store-DMBLD.litmus",
    "tests/D15347-store-DMBST.litmus",
    "tests/D15347-store-DSB-ISB.litmus",
    "tests/D15347-store-DSB.litmus",
    "tests/D15347-store-rel.litmus",
    "tests/D15347-store.litmus",
    "tests/DBchange-UP-STR-DSB-ISB.litmus",
    "tests/DBchange-UP-STR-DSB-TLBI-DSB-ISB.litmus",
    "tests/ExtTLBIAfter.litmus",
    "tests/F1.litmus",
    "tests/F1a.litmus",
    "tests/F1b.litmus",
    "tests/F1c+Fatal.litmus",
    "tests/F1c+Handled.litmus",
    "tests/F1d+Fatal.litmus",
    "tests/F1d+Handled.litmus",
    "tests/F1e+Fatal.litmus",
    "tests/F1e+Handled.litmus",
    "tests/F2+DSB-ETS.litmus",
    "tests/F2.litmus",
    "tests/F2.mod+BBM.litmus",
    "tests/F2.mod-MP-sync+dmb.ish.litmus",
    "tests/F2.mod-MP-sync.litmus",
    "tests/F2.mod-reduced+BBM.litmus",
    "tests/F2.mod-reduced-noncache.litmus",
    "tests/F2.mod-reduced-with-type+BBM.litmus",
    "tests/F2.mod-reduced-with-type.litmus",
    "tests/F2.mod-reduced.litmus",
    "tests/F2.mod-with-type+BBM-DSB-ISB.litmus",
    "tests/F2.mod-with-type+BBM.litmus",
    "tests/F2.mod-with-type+BBM2.litmus",
    "tests/F2.mod.litmus",
    "tests/F2S+DSB-ETS.litmus",
    "tests/F2S.litmus",
    "tests/F2Sdb+DSB-ETS.litmus",
    "tests/F2V.litmus",
    "tests/F3.litmus",
    "tests/F4.litmus",
    "tests/F5.litmus",
    "tests/F6.litmus",
    "tests/F7.litmus",
    "tests/F8.litmus",
    "tests/F9-tps-rrg.litmus",
    "tests/F9-tps.litmus",
    "tests/FA.litmus",
    "tests/FB.litmus",
    "tests/FC.litmus",
    "tests/FD.litmus",
    "tests/FE.litmus",
    "tests/FF.litmus",
    "tests/FG.litmus",
    "tests/FH.litmus",
    "tests/FI.litmus",
    "tests/FJ.litmus",
    "tests/FK.litmus",
    "tests/FL.litmus",
    "tests/FM.litmus",
    "tests/FN.litmus",
    "tests/FO.litmus",
    "tests/FP.litmus",
    "tests/G1.litmus",
    "tests/G2.litmus",
    "tests/G3.litmus",
    "tests/I2V-DSB-WEXP-DSB+obs+DSB-ISH-STR.litmus",
    "tests/I2V-DSB-WEXP-DSB-ISH-STR.litmus",
    "tests/I2V-R-DSB.ISH-ISB-R+W.litmus",
    "tests/I2V-R-DSB.ISH-ISB-W+W.litmus",
    "tests/I2V-R-DSB.LD-ISB-R+W.litmus",
    "tests/I2V-R-DSB.LD-ISB-W+W.litmus",
    "tests/I2V-R-DSB.ST-ISB-R+W.litmus",
    "tests/I2V-R-DSB.ST-ISB-W+W.litmus",
    "tests/I2V-UP-DSB-ISB.litmus",
    "tests/I2V-UP-DSB.litmus",
    "tests/I2V-UP-STR-DSB-ISB.litmus",
    "tests/I2V-UP-STR-DSB-TLBI-DSB-ISB.litmus",
    "tests/I2V-W-DSB.ISH-ISB-W.litmus",
    "tests/I2V-W-DSB.LD-ISB-R.litmus",
    "tests/I2V-W-DSB.LD-ISB-W.litmus",
    "tests/I2V-W-DSB.ST-ISB-R.litmus",
    "tests/I2V-W-DSB.ST-ISB-W.litmus",
    "tests/IRIW-I2Ipte+64.litmus",
    "tests/IRIW-I2Vpte+64.litmus",
    "tests/IRIW-V2Ipte+64.litmus",
    "tests/IRIW-V2Vpte+64.litmus",
    "tests/J-simple.litmus",
    "tests/J1.litmus",
    "tests/J2.litmus",
    "tests/J3.litmus",
    "tests/J3p.litmus",
    "tests/J4.litmus",
    "tests/J6.litmus",
    "tests/J7.litmus",
    "tests/J7p.litmus",
    "tests/Ja2-TLBIDSB.litmus",
    "tests/Ja2-ind.litmus",
    "tests/Ja2.litmus",
    "tests/Ja3-TLBIDSB.litmus",
    "tests/Ja3.litmus",
    "tests/Ja4-TLBIDSB.litmus",
    "tests/Ja4-ind.litmus",
    "tests/Ja4-mod-ind.litmus",
    "tests/Ja4-mod.litmus",
    "tests/Ja4.litmus",
    "tests/Ja5-TLBIDSB.litmus",
    "tests/Ja5.litmus",
    "tests/Jna-rel.litmus",
    "tests/Jna.litmus",
    "tests/LB+dmb.sy+addr-po-HUaf.litmus",
    "tests/LB+dmb.sy+addr-po-HUdb.litmus",
    "tests/LB+dmb.sy+addrisb-HU.litmus",
    "tests/LBNExpExp.litmus",
    "tests/LBNExpExpInv.litmus",
    "tests/LBNExpNExp+ExpNExp+BIS.litmus",
    "tests/LBNExpNExp+ExpNExp.litmus",
    "tests/LBNExpNExp+ExpNExp2-BIS-2.litmus",
    "tests/LBNExpNExp+ExpNExp2-BIS-3.litmus",
    "tests/LBNExpNExp+ExpNExp2-BIS.litmus",
    "tests/LBNExpNExp+ExpNExp2.litmus",
    "tests/LBNExpNExp+ExpNExp3.litmus",
    "tests/LBNExpNExp+ExpNExp4.litmus",
    "tests/LBNExpNExp+ExpNExp5.litmus",
    "tests/LBNExpNExp+ExpNExp6.litmus",
    "tests/LBNExpNExp+NExpNExp.litmus",
    "tests/LBNExpNExp.litmus",
    "tests/LDADD-AF-DB.litmus",
    "tests/LDADD-AF.litmus",
    "tests/LDCLRptex-LDRx+af.litmus",
    "tests/LDCLRptex-LDRx+af2.litmus",
    "tests/LDCLRptex-LDRx+af3.litmus",
    "tests/LDCLRptex-STRx+db+BIS.litmus",
    "tests/LDCLRptex-STRx+db.litmus",
    "tests/LDR+32.litmus",
    "tests/LDR-AF.litmus",
    "tests/LDR-AFv0.litmus",
    "tests/LDR-BY2PTE-0-LLSC.litmus",
    "tests/LDR-BY2PTE-0.litmus",
    "tests/LDR-BY2PTE-1.litmus",
    "tests/LDR-TLBI.litmus",
    "tests/LDR.litmus",
    "tests/LDRaf0-HA+32.litmus",
    "tests/LDRaf0-HA.litmus",
    "tests/LDRaf0-noHA.litmus",
    "tests/LDRaf0.litmus",
    "tests/LDRaf0db0dbm1.litmus",
    "tests/LDRaf1.litmus",
    "tests/LDRptex.litmus",
    "tests/LDRv0.litmus",
    "tests/LDRv1+32.litmus",
    "tests/LDRv1.litmus",
    "tests/LDRx+LDCLRptex+af.litmus",
    "tests/LDRx+LDR-BIC-STRptex.litmus",
    "tests/LDRx+LDSETptex+af.litmus",
    "tests/LDRx+STRptex+af.litmus",
    "tests/LDRx+STRptex+oa.litmus",
    "tests/LDRx+STRx-LDRptex+af.litmus",
    "tests/LDRx+STRx-STRptex+af.litmus",
    "tests/LDRx+STRx-STRptex+af2+BIS.litmus",
    "tests/LDRx+STRx-STRptex+af2-RO.litmus",
    "tests/LDRx+STRx-STRptex+af2-RW-RO.litmus",
    "tests/LDRx+STRx-STRptex+af2.litmus",
    "tests/LDRx+SWPptex+af.litmus",
    "tests/LDRx-LDRptex.litmus",
    "tests/LDRx-LDRptex2.litmus",
    "tests/LDRx-STRptex.litmus",
    "tests/LDRx-ctrl-DSB-ISB-STRptex+SWP-RO.litmus",
    "tests/LDRx-ctrl-DSB-ISB-STRptex-RO.litmus",
    "tests/LDRx-ctrl-DSB-STRptex+SWP-RO.litmus",
    "tests/LDRx-ctrl-DSB-STRptex-RO.litmus",
    "tests/LDRx-ctrl-ISB-DSB-ISB-STRptex+SWP-RO.litmus",
    "tests/LDRx-ctrl-ISB-DSB-ISB-STRptex-RO.litmus",
    "tests/LDRx-ctrl-TLBI-STRptex+SWP.litmus",
    "tests/LDRx-ctrl-TLBI-STRptex+SWPV2I.litmus",
    "tests/LDRx-ctrl-TLBI-STRptex-RO.litmus",
    "tests/LDRx-ctrl-TLBI-STRptex.litmus",
    "tests/LDRx-ctrl-TLBI-STRptexV2I.litmus",
    "tests/LDRxaf0-invalid.litmus",
    "tests/LLSC+HA.litmus",
    "tests/Luc00.litmus",
    "tests/MP+BBM+DSB-ISB+BIS.litmus",
    "tests/MP+DSB+DSB-ISB.litmus",
    "tests/MP+DSB+ctrl+32.litmus",
    "tests/MP+DSB+ctrl.litmus",
    "tests/MP+DSB-TLBI-DSB+DMBLD.litmus",
    "tests/MP+DSB.ST+DSB.LD-TLBI-DSB.litmus",
    "tests/MP+DSB.ST+acq-TLBI-DSB.litmus",
    "tests/MP+DSB.ST+addr-TLBI-DSB.litmus",
    "tests/MP+HA-DSB.ISH.litmus",
    "tests/MP+HA-DSB.LD.litmus",
    "tests/MP+HA-DSB.ST.litmus",
    "tests/MP+HD-DSB.ISH.litmus",
    "tests/MP+HD-DSB.LD.litmus",
    "tests/MP+HD-DSB.ST.litmus",
    "tests/MP+TLBI+DMBLD.litmus",
    "tests/MP+bbm+dmbld.litmus",
    "tests/MP+bbm+dsb-isb+VMALL.litmus",
    "tests/MP+bbm+dsb-isb.litmus",
    "tests/MP+dmb.st+ctrl-isb-tlbi-dsb-isb.litmus",
    "tests/MP+dmb.st+data.litmus",
    "tests/MP+dmb.st+dsb.ld-tlbi-dsb-isb.litmus",
    "tests/MP+dmb.st+dsb.ld-tlbi-noscope-dsb-isb.litmus",
    "tests/MP+dmb.st+dsb.st-tlbi-dsb-isb.litmus",
    "tests/MP+dmb.sy+addr-store-pos-addr+PTE+BIS.litmus",
    "tests/MP+dmb.sy+addr-store-pos-addr+PTE.litmus",
    "tests/MP+dmb.sy+addr-store-pos-addr+W+PTE.litmus",
    "tests/MP+dmb.sy+addr-store-pos-addr+W.litmus",
    "tests/MP+dmb.sy+addr-store-pos-addr.litmus",
    "tests/MP+dmb.sy+addrR-pos-addr+PTE+BIS.litmus",
    "tests/MP+dmb.sy+addrR-pos-addr+PTE.litmus",
    "tests/MP+dmb.sy+addrR-pos-addr+W+PTE.litmus",
    "tests/MP+dmb.sy+addrR-pos-addr+W.litmus",
    "tests/MP+dmb.sy+addrR-pos-addr.litmus",
    "tests/MP+dmbst-publish+dmbld.litmus",
    "tests/MP+pterfi-addr+dmb.ld.litmus",
    "tests/MP+rel+DSB.LD-TLBI-DSB.litmus",
    "tests/MP+rfi_pte-addr+dmb.ld.litmus",
    "tests/MP+shoot+DMBLD+VMALL.litmus",
    "tests/MP+shoot+DMBLD.litmus",
    "tests/MP+shoot+addr+VMALL.litmus",
    "tests/MP+shoot+addr.litmus",
    "tests/MP+shoot+dsb+VMALL.litmus",
    "tests/MP+shoot+dsb-isb+VMALL.litmus",
    "tests/MP+shoot+dsb-isb.litmus",
    "tests/MP+shoot+dsb.litmus",
    "tests/MP+shoot+po+VMALL.litmus",
    "tests/MP+shoot+po.litmus",
    "tests/MP-HU.litmus",
    "tests/MP-ISB1+64.litmus",
    "tests/MP-ISB2+64.litmus",
    "tests/MP-ISB3+64.litmus",
    "tests/MP-pte+DMBST+DMBLD.litmus",
    "tests/MP-pte+DSB-TLBI-DSB+DMBLD.litmus",
    "tests/MP-pte.litmus",
    "tests/MPExp-DMBST-Exp+Exp-DSB-ISB-NExp.litmus",
    "tests/MPExp-shoot-Exp+Exp-DMBLD-ISB-NExp+VMALL.litmus",
    "tests/MPExp-shoot-Exp+Exp-DMBLD-ISB-NExp.litmus",
    "tests/MPExp-shoot-Exp+Exp-DMBLD-NExp+VMALL.litmus",
    "tests/MPExp-shoot-Exp+Exp-DMBLD-NExp.litmus",
    "tests/MPExp-shoot-Exp+Exp-DMBLD-NExp2+VMALL.litmus",
    "tests/MPExp-shoot-Exp+Exp-DMBLD-NExp2.litmus",
    "tests/MPExp-shoot-Exp+Exp-DSB-ISB-NExp+VMALL.litmus",
    "tests/MPExp-shoot-Exp+Exp-DSB-ISB-NExp.litmus",
    "tests/MPI2V+rel+acq+64.litmus",
    "tests/MPI2V+shoot+dmbld.litmus",
    "tests/MPInv+dsb+dsb-isb.litmus",
    "tests/MPInv+shoot+dsb-isb+VMALL.litmus",
    "tests/MPInv+shoot+dsb-isb.litmus",
    "tests/MPV2I2V-no-bbm.litmus",
    "tests/MPV2V+dsb+dmbld+64.litmus",
    "tests/MPV2V+dsb+dmbst+64.litmus",
    "tests/MPV2V+dsb+dsb-isb+64.litmus",
    "tests/Marc02+DSB.litmus",
    "tests/Marc02.litmus",
    "tests/Marc03+BIS.litmus",
    "tests/Marc03.litmus",
    "tests/NOP+AF.litmus",
    "tests/NT-00-addr.litmus",
    "tests/NT-00-ctrl.litmus",
    "tests/NT-00-data.litmus",
    "tests/NT-01-addr.litmus",
    "tests/NT-01-ctrl.litmus",
    "tests/NT-01-data.litmus",
    "tests/NT-02-addr.litmus",
    "tests/NT-02-ctrl.litmus",
    "tests/NT-02-data.litmus",
    "tests/NT-03-addr.litmus",
    "tests/NT-03-ctrl.litmus",
    "tests/NT-03-data.litmus",
    "tests/NT-04-addr.litmus",
    "tests/NT-04-ctrl.litmus",
    "tests/NT-04-data.litmus",
    "tests/NT-05-addr.litmus",
    "tests/NT-05-ctrl.litmus",
    "tests/NT-06-af.litmus",
    "tests/NT-06-db.litmus",
    "tests/NT-07-af+OBS.litmus",
    "tests/NT-07-af.litmus",
    "tests/NT-07-db+OBS.litmus",
    "tests/NT-07-db.litmus",
    "tests/NT-08-af.litmus",
    "tests/NT-09-af.litmus",
    "tests/NT-0A-af.litmus",
    "tests/NT-0B-af+OBS.litmus",
    "tests/NT-0B-af.litmus",
    "tests/NT-0C-af.litmus",
    "tests/NT-0C-db.litmus",
    "tests/NT-10-addr+dsb.litmus",
    "tests/NT-10-addr.litmus",
    "tests/NT-10-ctrl+dsb.litmus",
    "tests/NT-10-ctrl.litmus",
    "tests/NT-10-data+dsb.litmus",
    "tests/NT-10-data.litmus",
    "tests/NT-10-dmb+dsb-isb.litmus",
    "tests/NT-10-dmb+dsb.litmus",
    "tests/NT-10-dmb.litmus",
    "tests/NT-10-dmbld+dsb.litmus",
    "tests/NT-10-dmbld.litmus",
    "tests/NT-10-dsb+dmbld-isb.litmus",
    "tests/NT-10-dsb+dsb.litmus",
    "tests/NT-10-dsb-isb+dmbld.litmus",
    "tests/NT-10-dsb.litmus",
    "tests/NT-10-dsball.litmus",
    "tests/NT-10-dsbld+dsb.litmus",
    "tests/NT-10-dsbld.litmus",
    "tests/NT-10-tlbi+dsb.litmus",
    "tests/NT-10-tlbi.litmus",
    "tests/NT-11-addr+dsb.litmus",
    "tests/NT-11-addr-allha+dsb.litmus",
    "tests/NT-11-addr-allha.litmus",
    "tests/NT-11-addr.litmus",
    "tests/NT-11-ctrl+dsb.litmus",
    "tests/NT-11-ctrl-allha+dsb.litmus",
    "tests/NT-11-ctrl-allha.litmus",
    "tests/NT-11-ctrl.litmus",
    "tests/NT-11-data+dsb.litmus",
    "tests/NT-11-data-allha+dsb.litmus",
    "tests/NT-11-data-allha.litmus",
    "tests/NT-11-data.litmus",
    "tests/NT-11-dmb+dsb.litmus",
    "tests/NT-11-dmb-allha+dsb.litmus",
    "tests/NT-11-dmb-allha.litmus",
    "tests/NT-11-dmb.litmus",
    "tests/NT-11-dmbld+dsb.litmus",
    "tests/NT-11-dmbld-allha+dsb.litmus",
    "tests/NT-11-dmbld-allha.litmus",
    "tests/NT-11-dmbld.litmus",
    "tests/NT-11-dsb+dsb.litmus",
    "tests/NT-11-dsb-allha+dsb.litmus",
    "tests/NT-11-dsb-allha.litmus",
    "tests/NT-11-dsb.litmus",
    "tests/NT-11-dsbld+dsb.litmus",
    "tests/NT-11-dsbld-allha+dsb.litmus",
    "tests/NT-11-dsbld-allha.litmus",
    "tests/NT-11-dsbld.litmus",
    "tests/NT-11-tlbi+dsb.litmus",
    "tests/NT-11-tlbi-allha+dsb.litmus",
    "tests/NT-11-tlbi-allha.litmus",
    "tests/NT-11-tlbi.litmus",
    "tests/NT-12-addr+dsb.litmus",
    "tests/NT-12-addr-allha+dsb.litmus",
    "tests/NT-12-addr-allha.litmus",
    "tests/NT-12-addr.litmus",
    "tests/NT-12-ctrl+dsb.litmus",
    "tests/NT-12-ctrl-allha+dsb.litmus",
    "tests/NT-12-ctrl-allha.litmus",
    "tests/NT-12-ctrl.litmus",
    "tests/NT-12-data+dsb.litmus",
    "tests/NT-12-data-allha+dsb.litmus",
    "tests/NT-12-data-allha.litmus",
    "tests/NT-12-data.litmus",
    "tests/NT-12-dmb+dsb.litmus",
    "tests/NT-12-dmb-allha+dsb.litmus",
    "tests/NT-12-dmb-allha-variant1-LLSC.litmus",
    "tests/NT-12-dmb-allha-variant1.litmus",
    "tests/NT-12-dmb-allha-variant2.litmus",
    "tests/NT-12-dmb-allha.litmus",
    "tests/NT-12-dmb.litmus",
    "tests/NT-12-dmbld+dsb.litmus",
    "tests/NT-12-dmbld-allha+dsb.litmus",
    "tests/NT-12-dmbld-allha.litmus",
    "tests/NT-12-dmbld.litmus",
    "tests/NT-12-dsb+dsb.litmus",
    "tests/NT-12-dsb-allha+dsb.litmus",
    "tests/NT-12-dsb-allha.litmus",
    "tests/NT-12-dsb.litmus",
    "tests/NT-12-dsbld+dsb.litmus",
    "tests/NT-12-dsbld-allha+dsb.litmus",
    "tests/NT-12-dsbld-allha.litmus",
    "tests/NT-12-dsbld.litmus",
    "tests/NT-12-tlbi+dsb.litmus",
    "tests/NT-12-tlbi-allha+dsb.litmus",
    "tests/NT-12-tlbi-allha.litmus",
    "tests/NT-12-tlbi.litmus",
    "tests/NT-13-dmb.litmus",
    "tests/NT-14-dmb.litmus",
    "tests/NT-20-addr+dsb.litmus",
    "tests/NT-20-addr.litmus",
    "tests/NT-20-ctrl+dsb.litmus",
    "tests/NT-20-ctrl.litmus",
    "tests/NT-20-data+dsb.litmus",
    "tests/NT-20-data.litmus",
    "tests/NT-20-dmb+dsb.litmus",
    "tests/NT-20-dmb.litmus",
    "tests/NT-20-dmbld+dsb.litmus",
    "tests/NT-20-dmbld.litmus",
    "tests/NT-20-dsb.litmus",
    "tests/NT-20-dsbld+dsb.litmus",
    "tests/NT-20-dsbld.litmus",
    "tests/NT-20-tlbi+dsb.litmus",
    "tests/NT-20-tlbi.litmus",
    "tests/NT-23-addr+dsb.litmus",
    "tests/NT-23-addr.litmus",
    "tests/NT-23-ctrl+dsb.litmus",
    "tests/NT-23-ctrl.litmus",
    "tests/NT-23-data+dsb.litmus",
    "tests/NT-23-data.litmus",
    "tests/NT-23-dmbld+dsb.litmus",
    "tests/NT-23-dmbld.litmus",
    "tests/NT-23-dsb.litmus",
    "tests/NT-23-tlbi+dsb.litmus",
    "tests/NT-23-tlbi.litmus",
    "tests/NT-30-addr+dsb.litmus",
    "tests/NT-30-addr.litmus",
    "tests/NT-30-ctrl+dsb.litmus",
    "tests/NT-30-ctrl.litmus",
    "tests/NT-30-data+dsb.litmus",
    "tests/NT-30-data.litmus",
    "tests/NT-30-dmb+dsb.litmus",
    "tests/NT-30-dmb+dsb2.litmus",
    "tests/NT-30-dmb.litmus",
    "tests/NT-30-dmbld+dsb.litmus",
    "tests/NT-30-dmbld.litmus",
    "tests/NT-30-dsb+dsb.litmus",
    "tests/NT-30-dsb.litmus",
    "tests/NT-30-dsbld+dsb.litmus",
    "tests/NT-30-dsbld.litmus",
    "tests/NT-30-tlbi+dsb.litmus",
    "tests/NT-30-tlbi-isb+dsb.litmus",
    "tests/NT-30-tlbi-isb.litmus",
    "tests/NT-30-tlbi.litmus",
    "tests/NT-33-addr+dsb.litmus",
    "tests/NT-33-addr.litmus",
    "tests/NT-33-ctrl+dsb.litmus",
    "tests/NT-33-ctrl.litmus",
    "tests/NT-33-data+dsb.litmus",
    "tests/NT-33-data.litmus",
    "tests/NT-33-dmbld+dsb.litmus",
    "tests/NT-33-dmbld+dsb2.litmus",
    "tests/NT-33-dmbld.litmus",
    "tests/NT-33-dsb+dsb.litmus",
    "tests/NT-33-dsb.litmus",
    "tests/NT-33-tlbi+dsb.litmus",
    "tests/NT-33-tlbi-isb+dsb.litmus",
    "tests/NT-33-tlbi-isb.litmus",
    "tests/NT-33-tlbi.litmus",
    "tests/PTE-SimpleETC.litmus",
    "tests/PTE-WRC.litmus",
    "tests/R3+W+32.litmus",
    "tests/R3+W.litmus",
    "tests/R3-DSBs+W+32.litmus",
    "tests/R3-DSBs+W.litmus",
    "tests/RW+RR-DMBLD+DMBLD-SWP.litmus",
    "tests/RW+RR-DMBLD+DMBLD-SWP2.litmus",
    "tests/RW+RR-DMBLD+DMBLD-SWP3.litmus",
    "tests/RW+RR-DMBLD+DMBLD-SWP4+WREG.litmus",
    "tests/RW+RR-DMBLD+DMBLD-SWP5.litmus",
    "tests/RW+RR-DMBLD+DMBLD.litmus",
    "tests/RW+RR-DSB+DMBLD.litmus",
    "tests/RW+RR-DSB+DSB+WREG.litmus",
    "tests/RW+RR.litmus",
    "tests/RW+RRpte-DMBLD+DMBLD-SWP.litmus",
    "tests/RW+RRpte-DMBLD+DMBLD.litmus",
    "tests/RW+RRpte-DMBLD+DSB.litmus",
    "tests/RW+RRpte-DSB+DMBLD+WREG.litmus",
    "tests/RW+RRpte-addr+DMBLD.litmus",
    "tests/RWNExpExp+DSB.litmus",
    "tests/RWNExpExp.litmus",
    "tests/RWpte+W.litmus",
    "tests/RaR-PTE.litmus",
    "tests/S+dmb.st+addr-HUaf.litmus",
    "tests/S+dmb.st+addr-HUdb.litmus",
    "tests/S+dmb.st+data-HUaf.litmus",
    "tests/S+dmb.st+data-HUdb.litmus",
    "tests/S+dmb.st+dmb-HUaf.litmus",
    "tests/S+dmb.st+dsb-HUaf.litmus",
    "tests/S+dmb.st+dsb.ish-isb-HUaf.litmus",
    "tests/S+dmb.st+dsb.ld-tlbi-dsb-isb.litmus",
    "tests/S+dmb.st+dsb.st-tlbi-dsb-isb.litmus",
    "tests/SNExpExpExpNExp+DSB+DSB3.litmus",
    "tests/STR+32.litmus",
    "tests/STR-AF-DB.litmus",
    "tests/STR-AF.litmus",
    "tests/STR-DB.litmus",
    "tests/STR-DSB-ISB.litmus",
    "tests/STR-LDR-I2V.litmus",
    "tests/STR-TLBI+VMALL.litmus",
    "tests/STR-TLBI.litmus",
    "tests/STR-db0+dbm1-HD.litmus",
    "tests/STR-db0-noHD+32.litmus",
    "tests/STR-db0-noHD.litmus",
    "tests/STR.litmus",
    "tests/STRaf0.litmus",
    "tests/STRaf1.litmus",
    "tests/STRaf1db0dbm0.litmus",
    "tests/STRaf1db0dbm1.litmus",
    "tests/STRaf1db1.litmus",
    "tests/STRdb0dbm1.litmus",
    "tests/STRptex+AF.litmus",
    "tests/STRptex+AF0+BIS.litmus",
    "tests/STRptex+AF0.litmus",
    "tests/STRv0+af.litmus",
    "tests/STRv0+db.litmus",
    "tests/STRv0.litmus",
    "tests/STRva-STRpte.litmus",
    "tests/STRva-STRpte2.litmus",
    "tests/STRx+2LDSETptex+db+TLBI.litmus",
    "tests/STRx+2LDSETptex+db.litmus",
    "tests/STRx+2LDSETptex+db2.litmus",
    "tests/STRx+2LDSETptex+db3.litmus",
    "tests/STRx+2SWPptex+db+TLBI.litmus",
    "tests/STRx+2SWPptex+db.litmus",
    "tests/STRx+2SWPptex+db2.litmus",
    "tests/STRx+2SWPptex+db3.litmus",
    "tests/STRx+LDCLRptex+af.litmus",
    "tests/STRx+LDCLRptex+db.litmus",
    "tests/STRx+LDR-ORR-STRptex.litmus",
    "tests/STRx+LDR-STRptex+af.litmus",
    "tests/STRx+LDR-STRptex+db.litmus",
    "tests/STRx+LDR-STRptex+db2.litmus",
    "tests/STRx+LDRx-ptex+af.litmus",
    "tests/STRx+LDRx-ptex+db.litmus",
    "tests/STRx+STCLRptex+af.litmus",
    "tests/STRx+STCLRptex+db+dbm.litmus",
    "tests/STRx+STCLRptex+db.litmus",
    "tests/STRx+STCLRptex+db2+dbm.litmus",
    "tests/STRx+STCLRptex+db2.litmus",
    "tests/STRx+STCLRptex+db3+dbm.litmus",
    "tests/STRx+STCLRptex+db3.litmus",
    "tests/STRx+STCLRptex+db4.litmus",
    "tests/STRx+STRptex+oa.litmus",
    "tests/STRx+SWPptex+af.litmus",
    "tests/STRx+SWPptex+db.litmus",
    "tests/STRx+SWPptex+db2.litmus",
    "tests/STRx+SWPptex+db3.litmus",
    "tests/STRx+SWPptex+db4.litmus",
    "tests/STRx+SWPptex+db5.litmus",
    "tests/STRx+SWPptex1.litmus",
    "tests/STRx+SWPptex2.litmus",
    "tests/STRx+SWPptexForbid.litmus",
    "tests/STRx+SWPptexForbid1.litmus",
    "tests/STRx+SWPptexForbid2.litmus",
    "tests/STRx-LDRptex.litmus",
    "tests/STRx-LDRptex2.litmus",
    "tests/STRx-LDRptex3.litmus",
    "tests/STRx-LDRptex4.litmus",
    "tests/SWP-AF-DB.litmus",
    "tests/SWP-AF.litmus",
    "tests/SWP-RpteW+RR+DMBLD+DMBLD-P0HD.litmus",
    "tests/SWP-RpteW+RR+DMBLD+DMBLD-P0noHD.litmus",
    "tests/SWPptex+AF.litmus",
    "tests/SWPptex+AF0.litmus",
    "tests/Sc01.litmus",
    "tests/Sc02.litmus",
    "tests/Sc03.litmus",
    #"tests/Sc04+BIS.litmus",
    #"tests/Sc04.litmus",
    #"tests/Sc05+BIS.litmus",
    #"tests/Sc05.litmus",
    #"tests/Sc06+BIS.litmus",
    #"tests/Sc06.litmus",
    #"tests/Sc07+BIS.litmus",
    #"tests/Sc07.litmus",
    #"tests/Sc08+BIS.litmus",
    #"tests/Sc09+BIS.litmus",
    "tests/SpecAF.litmus",
    "tests/SpecSpecAF+Fault.litmus",
    "tests/SpecSpecAF.litmus",
    "tests/TA1.litmus",
    "tests/TA2.litmus",
    "tests/TA3.litmus",
    "tests/TST-EL0-PTE.litmus",
    "tests/TST-EL0.litmus",
    "tests/TwoPhantoms.litmus",
    "tests/V2I+VMALL.litmus",
    "tests/V2I-R-DSB.LD-TLBI-DSB.ISH-ISB-R+W.litmus",
    "tests/V2I-R-DSB.ST-TLBI-DSB.ISH-ISB-R+W.litmus",
    "tests/V2I-RW+W.litmus",
    "tests/V2I-RW+WR.litmus",
    "tests/V2I-UP-DSB-TLBI-DSB+VMALL.litmus",
    "tests/V2I-UP-DSB-TLBI-DSB-ISB+VMALL.litmus",
    "tests/V2I-UP-DSB-TLBI-DSB-ISB.litmus",
    "tests/V2I-UP-DSB-TLBI-DSB-ISB2.litmus",
    "tests/V2I-UP-DSB-TLBI-DSB.litmus",
    "tests/V2I-W+R-CTRL-ISB-TLBI-DSB.ISH-ISB-R.litmus",
    "tests/V2I-W-DSB.ISH-TLBI-DSB.ISH-ISB-W.litmus",
    "tests/V2I-W-DSB.ISH-TLBI-DSB.ISH-R+WR.litmus",
    "tests/V2I-W-DSB.ISH-TLBI-DSB.ISH-W+RR.litmus",
    "tests/V2I-W-DSB.ISH-TLBI-DSB.LD-ISB-R.litmus",
    "tests/V2I-W-DSB.ISH-TLBI-DSB.LD-ISB-W.litmus",
    "tests/V2I-W-DSB.ISH-TLBI-DSB.LD-R+WR.litmus",
    "tests/V2I-W-DSB.ISH-TLBI-DSB.LD-W+RR.litmus",
    "tests/V2I-W-DSB.ISH-TLBI-DSB.ST-ISB-R.litmus",
    "tests/V2I-W-DSB.ISH-TLBI-DSB.ST-ISB-W.litmus",
    "tests/V2I-W-DSB.ISH-TLBI-DSB.ST-R+WR.litmus",
    "tests/V2I-W-DSB.ISH-TLBI-DSB.ST-W+RR.litmus",
    "tests/V2I-W-DSB.LD-TLBI-DSB.ISH-ISB-R.litmus",
    "tests/V2I-W-DSB.ST-TLBI-DSB.ISH-ISB-R.litmus",
    "tests/V2I-load-DSB-ISB.litmus",
    "tests/V2I.litmus",
    "tests/VIS01-load.litmus",
    "tests/VIS01-load2.litmus",
    "tests/VIS01-store.litmus",
    "tests/VIS7+DSB.litmus",
    "tests/VIS7+SY.litmus",
    "tests/VIS7+TLBI+VMALL.litmus",
    "tests/VIS7+TLBI.litmus",
    "tests/VIS7+TLBI2.litmus",
    "tests/VIS7.litmus",
    "tests/VW+VW+VW+3R.litmus",
    "tests/W-DSB-TLBI-DSB.litmus",
    "tests/W1.litmus",
    "tests/WNExp+RWNExpExp+DSB.litmus",
    "tests/WNExp+RWNExpExp+DSB2.litmus",
    "tests/WNExp+RWNExpExp+DSB3.litmus",
    "tests/WNExp.litmus",
    "tests/WNExp2.litmus",
    "tests/WNExpWExp+DSB.litmus",
    "tests/WRC+dsb-isb+dsb-isb.litmus",
    "tests/WRC+shoot+DSB.litmus",
    "tests/WRC+shoot+dsb-isb+VMALL.litmus",
    "tests/WRC+shoot+dsb-isb.litmus",
    "tests/WRCpte5.litmus",
    "tests/coRR+HA-DSB.ISH.litmus",
    "tests/coRR+HA-DSB.LD.litmus",
    "tests/coRR+HA-DSB.ST.litmus",
    "tests/coRR+W-DSB-TLBI-DSB+ob-W.litmus",
    "tests/coRR+W-DSB-TLBI-DSB-HU+rfe-W.litmus",
    "tests/coRR+W-DSB-TLBI-DSB-ISB-HU+rfe-W.litmus",
    "tests/coRR-pte+BIS.litmus",
    "tests/coRR-pte+BISA.litmus",
    "tests/coRR-pte.litmus",
    "tests/coRR-pte10.litmus",
    "tests/coRR-pte11+BIS.litmus",
    "tests/coRR-pte11.litmus",
    "tests/coRR-pte12.litmus",
    "tests/coRR-pte13.litmus",
    "tests/coRR-pte14.litmus",
    "tests/coRR-pte15.litmus",
    "tests/coRR-pte16-UP+ISB.litmus",
    "tests/coRR-pte16-UP+ISB2.litmus",
    "tests/coRR-pte16-UP-simple.litmus",
    "tests/coRR-pte16-UP.litmus",
    "tests/coRR-pte16.litmus",
    "tests/coRR-pte17.litmus",
    "tests/coRR-pte2.litmus",
    "tests/coRR-pte3.litmus",
    "tests/coRR-pte4.litmus",
    "tests/coRR-pte5.litmus",
    "tests/coRR-pte6+VMALL.litmus",
    "tests/coRR-pte6.litmus",
    "tests/coRR-pte7+BIS.litmus",
    "tests/coRR-pte7+VMALL.litmus",
    "tests/coRR-pte7.litmus",
    "tests/coRR-pte8-dmb.litmus",
    "tests/coRR-pte8-dsb-isb.litmus",
    "tests/coRR-pte8-dsb.litmus",
    "tests/coRR-pte8.litmus",
    "tests/coRR-pte9+VMALL.litmus",
    "tests/coRR-pte9+noscope.litmus",
    "tests/coRR-pte9-bis1.litmus",
    "tests/coRR-pte9-bis2.litmus",
    "tests/coRR-pte9-nobbm+dsb.litmus",
    "tests/coRR-pte9-nobbm.litmus",
    "tests/coRR-pte9-ob.litmus",
    "tests/coRR-pte9-plus8.litmus",
    "tests/coRR-pte9.litmus",
    "tests/coRR-pte9_1-bis1.litmus",
    "tests/coRR-pteA.litmus",
    "tests/coRRExpNExp+DMBLD.litmus",
    "tests/coRRExpNExp+DSB-ISB+BIS.litmus",
    "tests/coRRExpNExp+DSB-ISB.litmus",
    "tests/coRRExpNExp+DSB-TLBI-DSB+VMALL.litmus",
    "tests/coRRExpNExp+DSB-TLBI-DSB.litmus",
    "tests/coRRExpNExp+DSB-TLBI-DSB2+VMALL.litmus",
    "tests/coRRExpNExp+DSB-TLBI-DSB2.litmus",
    "tests/coRRExpNExp+DSB.LD-TLBI-DSB-ISB.litmus",
    "tests/coRRExpNExp+DSB.ST-TLBI-DSB-ISB.litmus",
    "tests/coRRExpNExp.litmus",
    "tests/coRRNExpNExpExp+DMB.litmus",
    "tests/coRRNExpNExpExp+DMB3.litmus",
    "tests/coRRNExpNExpExp+DMB7.litmus",
    "tests/coRRNExpNExpExp+DMB8.litmus",
    "tests/coRRNExpNExpExp+DSB.litmus",
    "tests/coRRNExpNExpExp+DSB2-noHD.litmus",
    "tests/coRRNExpNExpExp+DSB2.litmus",
    "tests/coRRNExpNExpExp+DSB3.litmus",
    "tests/coRRNExpNExpExp+DSB5.litmus",
    "tests/coRRNExpNExpExp+DSB6+BIS.litmus",
    "tests/coRRNExpNExpExp+DSB6+TER.litmus",
    "tests/coRRNExpNExpExp+DSB6+TER2.litmus",
    "tests/coRRNExpNExpExp+DSB6.litmus",
    "tests/coRRNExpNExpExp+DSB7.litmus",
    "tests/coRRNExpNExpExp+DSB8.litmus",
    "tests/coRRNExpNExpExp+addr.litmus",
    "tests/coRRNexpExp+DSB+AF.litmus",
    "tests/coRW-DB.litmus",
    "tests/coRWExpNExp.litmus",
    "tests/coRWImpExp+32.litmus",
    "tests/coRWImpExp+WExp+32.litmus",
    "tests/coRWImpExp+WExp.litmus",
    "tests/coRWImpExp.litmus",
    "tests/coRWWRNExpExpExpExp+DSB-DSB-DSB.litmus",
    "tests/coRWWRNExpExpExpExp+DSB-DSB-TLBI-DSB-DSB+VMALL.litmus",
    "tests/coRWWRNExpExpExpExp+DSB-DSB-TLBI-DSB-DSB.litmus",
    "tests/coRmwWExpNExp.litmus",
    "tests/coW-DSB-ob-TLBI-DSB-W.litmus",
    "tests/coW-DSB-ob-TLBI-W.litmus",
    "tests/coW-TLBI-W.litmus",
    "tests/coWR-pte.litmus",
    "tests/coWRExpNExp+DSB-ISB.litmus",
    "tests/coWRExpNExp+DSB-TLBI-DSB+VMALL.litmus",
    "tests/coWRExpNExp+DSB-TLBI-DSB.litmus",
    "tests/coWRExpNExp.litmus",
    "tests/coWRRNExpNExpExp+DSB.litmus",
    "tests/coWWExp-TLBI-NExp+VMALL.litmus",
    "tests/coWWExp-TLBI-NExp.litmus",
    "tests/coWWExpNExp.litmus",
    "tests/coWWRExpNExpExp+DSB-TLBI-DSB+VMALL.litmus",
    "tests/coWWRExpNExpExp+DSB-TLBI-DSB.litmus",
    "tests/coWWRExpNExpExp+DSB.litmus",
    "tests/coWWRExpNExpExp.litmus",
    "tests/coWWWNexpExpNexp+DSB-DSB-TLBI-DSB+VMALL.litmus",
    "tests/coWWWNexpExpNexp+DSB-DSB-TLBI-DSB.litmus",
    "tests/coWWWNexpExpNexp+DSB-DSB.litmus",
    "tests/load-valid.litmus",
    "tests/load-xy.litmus",
    "tests/miniMarc03.litmus",
    "tests/miniMarc04.litmus",
    "tests/miniMarc05.litmus",
    "tests/nBBM+LDR.litmus",
    "tests/needTLBI1.litmus",
    "tests/needTLBI2.litmus",
    "tests/permchange-M-shoot+DMB.ISH.litmus",
    "tests/newlob/LB+dmb.sy+acq-HU.litmus",
    "tests/newlob/LB+dmb.sy+dmb.sy-HU.litmus",
    "tests/newlob/LB+dmb.sy+dsb.sy-HU.litmus",
    "tests/newlob/LB+dmb.sy+dsb.sy-isb-HU.litmus",
    "tests/newlob/LB+dmb.sy+pickaddr-po-HUdb.litmus",
    "tests/newlob/LB+dmb.sy+rel-HU.litmus",
    "tests/newlob/MP+dmb.ish+scope-tlbi.vmall-dsb.ish-isb.litmus",
    "tests/newlob/MP+dmb.st+addr-tlbi-dsb.ish-isb.litmus",
    "tests/newlob/MP+dmb.st+addrisb-Imp_TTD_R.litmus",
    "tests/newlob/MP+dmb.st+tlbi.vmall-dsb.ish-isb.litmus",
    "tests/newlob/MP.I2V+dmb.st+swpal-po.litmus",
    "tests/newlob/MP.I2V+dmb.st+swpl-acq.litmus",
    "tests/newlob/RWRR+HU-dmb.sy+acq.litmus",
    "tests/newlob/RWRR+HU-dsb.sy+acq.litmus",
    "tests/newlob/RWRR+HU-rel+acq.litmus",
    "tests/newlob/S+dmb.st+ctrl-HUdb.litmus",
    "tests/newlob/S+dmb.st+pickaddr-HUdb.litmus",
    "tests/newlob/S+dmb.st+pickctrl-HUdb.litmus",
    "tests/newlob/S+dsb.st-tlbi.vae1is-dsb.ish+addr-HUaf.litmus",
    # "tests/newlob/S+dsb.sy-tlbi-dsb.sy+ctrl.litmus",
    "tests/newlob/S+dsb.sy-tlbi-dsb.sy+data_db0.litmus",
    # "tests/newlob/S-I2V+dmb.st+ctrl_Imp_TTD_R.litmus",
    "tests/newlob/S-I2V+dmb.st+data_Imp_TTD_R.litmus",
    "tests/newlob/V2I-W+R-CTRL-TLBI-DSB.ISH-ISB-R.litmus",
    "tests/newlob/coWR+HU-dsb.ld-Imp_TTD_R.litmus",
    "tests/newlob/coWR+HU-dsb.st-Imp_TTD_R.litmus",
    "tests/newlob/coWR+HU-dsb.sy-Imp_TTD_R.litmus",
    "tests/order-to-faults/2+2W+shoot+acqrel_mmufault_db.litmus",
    "tests/order-to-faults/2+2W+shoot+dmb.st_mmufault_db.litmus",
    "tests/order-to-faults/2+2W+shoot+dmb.sy_mmufault_db.litmus",
    "tests/order-to-faults/2+2W+shoot+po-mmufault_db.litmus",
    "tests/order-to-faults/2+2W+shoot+rel_mmufault_db.litmus",
    "tests/order-to-faults/MP+shoot+addrlrs-mmufault_af.litmus",
    "tests/order-to-faults/MP+shoot+datalrs-mmufault_af.litmus",
    "tests/order-to-faults/R+shoot+dmb.st-mmufault_af.litmus",
    "tests/order-to-faults/R+shoot+rel-acq-mmufault.litmus",
    "tests/order-to-faults/S+shoot+acq_mmufault_db.litmus",
    "tests/order-to-faults/S+shoot+acqrel_mmufault_db.litmus",
    "tests/order-to-faults/S+shoot+addr_mmufault_db.litmus",
    "tests/order-to-faults/S+shoot+addrpo_mmufault_db.litmus",
    # "tests/order-to-faults/S+shoot+ctrl_mmufault_db.litmus",
    "tests/order-to-faults/S+shoot+data_mmufault_db.litmus",
    "tests/order-to-faults/S+shoot+dmb.ld_mmufault_db.litmus",
    "tests/order-to-faults/S+shoot+dmb.sy_mmufault_db.litmus",
    "tests/order-to-faults/S+shoot+dsb.ld-mmufault_db.litmus",
    "tests/order-to-faults/S+shoot+pickaddr_mmufault_db.litmus",
    "tests/order-to-faults/S+shoot+pickaddrpo_mmufault_db.litmus",
    # "tests/order-to-faults/S+shoot+pickctrl_mmufault_db.litmus",
    "tests/order-to-faults/S+shoot+pickdata_mmufault_db.litmus",
    "tests/order-to-faults/S+shoot+po-mmufault_db.litmus",
    "tests/order-to-faults/S+shoot+rel_mmufault_db.litmus",
    "tests/order-to-faults/S+shoot+swpal-mmufault.litmus",
    "tests/order-to-faults/WRWW+shoot+po-mmufault_db.litmus",
    "tests/order-via-faults/MP+rel+po-mmufault_db-po.litmus",
    "tests/order-via-faults/MP-via_fault_STLR.litmus",
    "tests/order-via-faults/R+rel+po-mmufault_db-po.litmus",
    "tests/order-via-faults/R-via_fault_STLR.litmus",
    "tests/order-via-faults/R-via_fault_STR-2.litmus",
    "tests/order-via-faults/R-via_fault_STR-mod1.litmus",
    "tests/order-via-faults/R-via_fault_STR-mod2.litmus",
    "tests/order-via-faults/R-via_fault_STR-mod3.litmus",
    "tests/order-via-faults/R-via_fault_STR-with-DSB.litmus",
    "tests/order-via-faults/R-via_fault_STR.litmus",
    "tests/order-via-faults/SB+dmb.sy+po-mmufault_db-po.litmus",
    "tests/order-via-faults/bob/2+2W+rel+dmb.st-mmufault-po.litmus",
    "tests/order-via-faults/bob/2+2W+rel+dmb.st-mmufault_db-po.litmus",
    "tests/order-via-faults/bob/2+2W+rel+rel-mmufault-po.litmus",
    "tests/order-via-faults/bob/2+2W+rel+rel-mmufault_db-po.litmus",
    "tests/order-via-faults/bob/MP+rel+acq_rr-mmufault-po.litmus",
    "tests/order-via-faults/bob/MP+rel+acq_rw-mmufault-po.litmus",
    "tests/order-via-faults/bob/MP+rel+acq_rw-mmufault_db-po.litmus",
    "tests/order-via-faults/bob/MP+rel+acqpc_rr-mmufault-po.litmus",
    "tests/order-via-faults/bob/MP+rel+acqpc_rw-mmufault-po.litmus",
    "tests/order-via-faults/bob/MP+rel+acqpc_rw-mmufault_db-po.litmus",
    "tests/order-via-faults/bob/MP+rel+acqrel-mmufault_db-po.litmus",
    "tests/order-via-faults/bob/MP+rel+dmb.ld_rr-mmufault-po.litmus",
    "tests/order-via-faults/bob/MP+rel+dmb.ld_rw-mmufault-po.litmus",
    "tests/order-via-faults/bob/MP+rel+dmb.ld_rw-mmufault_db-po.litmus",
    "tests/order-via-faults/bob/MP+rel+dmb.sy_rr-mmufault-po.litmus",
    "tests/order-via-faults/bob/MP+rel+dmb.sy_rw-mmufault-po.litmus",
    "tests/order-via-faults/bob/MP+rel+dmb.sy_rw-mmufault_db-po.litmus",
    "tests/order-via-faults/bob/MP+rel+rel-mmufault-po.litmus",
    "tests/order-via-faults/bob/MP+rel+rel-mmufault_db-po.litmus",
    "tests/order-via-faults/bob/R+rel+acqrel-mmufault_db-po.litmus",
    "tests/order-via-faults/bob/R+rel+dmb.st-mmufault-po.litmus",
    "tests/order-via-faults/bob/R+rel+dmb.st-mmufault_db-po.litmus",
    "tests/order-via-faults/bob/R+rel+dmb.sy_wr-mmufault-po.litmus",
    "tests/order-via-faults/bob/R+rel+dmb.sy_ww-mmufault-po.litmus",
    "tests/order-via-faults/bob/R+rel+dmb.sy_ww-mmufault_db-po.litmus",
    "tests/order-via-faults/bob/R+rel+rel-acq-mmufault-po.litmus",
    "tests/order-via-faults/bob/R+rel+rel-mmufault-po.litmus",
    "tests/order-via-faults/bob/R+rel+rel-mmufault_db-po.litmus",
    "tests/order-via-faults/bob/R+rel+swpal_wr-mmufault-po.litmus",
    "tests/order-via-faults/bob/R+rel+swpal_ww-mmufault-po.litmus",
    "tests/order-via-faults/bob/R+rel+swpal_ww-mmufault_db-po.litmus",
    "tests/order-via-faults/cse-ob/MP+rel+ctrlisb-mmufault-po.litmus",
    "tests/order-via-faults/cse-ob/MP+rel+dsb.ld-isb-mmufault-po.litmus",
    "tests/order-via-faults/cse-ob/MP+rel+dsb.sy-isb-mmufault-po.litmus",
    "tests/order-via-faults/cse-ob/MP+rel+pickctrlisb-mmufault-po.litmus",
    "tests/order-via-faults/cse-ob/R+rel+dsb.st-isb-mmufault-po.litmus",
    "tests/order-via-faults/cse-ob/R+rel+dsb.sy-isb-mmufault-po.litmus",
    "tests/order-via-faults/dob/MP+rel+addr-mmufault-po.litmus",
    "tests/order-via-faults/dob/MP+rel+addr-mmufault_db-po.litmus",
    "tests/order-via-faults/dob/MP+rel+addrR-mmufault-po.litmus",
    "tests/order-via-faults/dob/MP+rel+addrlrs-mmufault-po.litmus",
    "tests/order-via-faults/dob/MP+rel+addrpo-mmufault-po.litmus",
    "tests/order-via-faults/dob/MP+rel+addrpo-mmufault_db-po.litmus",
    "tests/order-via-faults/dob/MP+rel+addrpoisb-mmufault-po.litmus",
    "tests/order-via-faults/dob/MP+rel+ctrlR-mmufault-po.litmus",
    "tests/order-via-faults/dob/MP+rel+ctrlW-mmufault-po.litmus",
    "tests/order-via-faults/dob/MP+rel+ctrlW-mmufault_db-po.litmus",
    "tests/order-via-faults/dob/MP+rel+data-mmufault-po.litmus",
    "tests/order-via-faults/dob/MP+rel+data-mmufault_db-po.litmus",
    "tests/order-via-faults/dob/MP+rel+datalrs-mmufault-po.litmus",
    "tests/order-via-faults/dsb-ob/MP+rel+dsb.ld_rr-mmufault-po.litmus",
    "tests/order-via-faults/dsb-ob/MP+rel+dsb.ld_rw-mmufault-po.litmus",
    "tests/order-via-faults/dsb-ob/MP+rel+dsb.ld_rw-mmufault_db-po.litmus",
    "tests/order-via-faults/dsb-ob/MP+rel+dsb.sy_rr-mmufault-po.litmus",
    "tests/order-via-faults/dsb-ob/MP+rel+dsb.sy_rw-mmufault-po.litmus",
    "tests/order-via-faults/dsb-ob/MP+rel+dsb.sy_rw-mmufault_db-po.litmus",
    "tests/order-via-faults/dsb-ob/R+rel+dsb.st_wr-mmufault-po.litmus",
    "tests/order-via-faults/dsb-ob/R+rel+dsb.st_ww-mmufault-po.litmus",
    "tests/order-via-faults/dsb-ob/R+rel+dsb.st_ww-mmufault_db-po.litmus",
    "tests/order-via-faults/dsb-ob/R+rel+dsb.sy_wr-mmufault-po.litmus",
    "tests/order-via-faults/dsb-ob/R+rel+dsb.sy_ww-mmufault-po.litmus",
    "tests/order-via-faults/dsb-ob/R+rel+dsb.sy_ww-mmufault_db-po.litmus",
    "tests/order-via-faults/lws/MP+rel+lws-mmufault-po.litmus",
    "tests/order-via-faults/lws/MP+rel+lws-mmufault_db-po.litmus",
    "tests/order-via-faults/lws/R+rel+lws-mmufault-po.litmus",
    "tests/order-via-faults/lws/R+rel+lws-mmufault_db-po.litmus",
    "tests/order-via-faults/pick-lob/MP+rel+pickdata-lrs-data-mmufault-po.litmus",
    "tests/order-via-faults/pick-lob/MP+rel+pickdata-lrs-data-mmufault_db-po.litmus",
    "tests/order-via-faults/pick-lob/R+rel+rmw-lrs-acq-mmufault-po.litmus",
    "tests/order-via-faults/pob/MP+rel+pickaddr-mmufault-po.litmus",
    "tests/order-via-faults/pob/MP+rel+pickaddr-mmufault_db-po.litmus",
    "tests/order-via-faults/pob/MP+rel+pickaddrR-mmufault-po.litmus",
    "tests/order-via-faults/pob/MP+rel+pickaddrpo-mmufault-po.litmus",
    "tests/order-via-faults/pob/MP+rel+pickaddrpo-mmufault_db-po.litmus",
    "tests/order-via-faults/pob/MP+rel+pickaddrpoisb-mmufault-po.litmus",
    "tests/order-via-faults/pob/MP+rel+pickctrlR-mmufault-po.litmus",
    "tests/order-via-faults/pob/MP+rel+pickctrlW-mmufault-po.litmus",
    "tests/order-via-faults/pob/MP+rel+pickctrlW-mmufault_db-po.litmus",
    "tests/order-via-faults/pob/MP+rel+pickdata-mmufault-po.litmus",
    "tests/order-via-faults/pob/MP+rel+pickdata-mmufault_db-po.litmus",
    "tests/order-via-faults/pob/MP+rel+pickdata_rmw-mmufault-po.litmus",
    "tests/order-via-faults/pob/MP+rel+pickdata_rmw-mmufault_db-po.litmus",
]
