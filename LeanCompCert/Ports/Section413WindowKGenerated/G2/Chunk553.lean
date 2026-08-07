import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk553

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582056240125709, 360582075582593680⟩, ⟨(-14640884588100966), (-13918190593531384)⟩, true⟩

def state01 : KState := ⟨⟨360579020531886822, 360579039881613770⟩, ⟨153326640838307578, 154049736290580602⟩, true⟩

def words00 : List Nat := [360581824016049143, 360581824337884603, 360581824836195675, 360581825334636158, 360581825553839309, 360581825554608637, 360581825448039994, 360581825333951951, 360581825219638397, 360581825087476916]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 55300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 55300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567518032716657, 360567537389770285⟩, ⟨789642467253556494, 790365967980940888⟩, true⟩

def words01 : List Nat := [360581825037807009, 360581824802540279, 360581824657150000, 360581825002206108, 360581825063679739, 360581825125272452, 360581825125958003, 360581825024599962, 360581824812164643, 360581824554773556]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 55310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 55300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360563637888820967, 360563657253131023⟩, ⟨1004191112205013628, 1004915014394939196⟩, true⟩

def words02 : List Nat := [360581824297147451, 360581824029702079, 360581823507517579, 360581822822903420, 360581822138189214, 360581821368411573, 360581820762026874, 360581820382967783, 360581820003819693, 360581819461957970]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 55320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 55300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360616744543590754, 360616763915158145⟩, ⟨(-1934513509492101834), (-1933789205718341118)⟩, true⟩

def words03 : List Nat := [360581819134333729, 360581819132762711, 360581819454324561, 360581819547074422, 360581819547799016, 360581819319619674, 360581819188134075, 360581819494690297, 360581820126762379, 360581820758986079]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 55330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 55300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360607988450518887, 360608007829435316⟩, ⟨(-1449956134073894763), (-1449231423570230287)⟩, true⟩

def words04 : List Nat := [360581821108070875, 360581821573425788, 360581822364321441, 360581823155414407, 360581823864078668, 360581824247660467, 360581824429599529, 360581824611614741, 360581824785663901, 360581825259588878]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 55340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 55300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360600302234444688, 360600321620611778⟩, ⟨(-1024392266619366074), (-1023667154755004812)⟩, true⟩

def words05 : List Nat := [360581826058855410, 360581826858248242, 360581827494736122, 360581828036937557, 360581828496881813, 360581828957028205, 360581829688881538, 360581830187651935, 360581830522365976, 360581830857172624]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 55350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 55300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608212793394320, 360608232186844019⟩, ⟨(-1462452812399723427), (-1461727297334233401)⟩, true⟩

def words06 : List Nat := [360581831179097660, 360581831664605369, 360581831979128479, 360581832293772696, 360581832330420338, 360581832377408638, 360581832522342027, 360581832667501081, 360581832921135774, 360581833398717848]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 55360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 55300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607861061005489, 360607880461787146⟩, ⟨(-1442934552578699680), (-1442208631506279388)⟩, true⟩

def words07 : List Nat := [360581833713475876, 360581834028306723, 360581834668322581, 360581835557745166, 360581836358631996, 360581837159614855, 360581837713082617, 360581837941790464, 360581838412664769, 360581838883781941]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 55370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 55300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360606707359068230, 360606726767104166⟩, ⟨(-1379072281180314880), (-1378345958330065652)⟩, true⟩

def words08 : List Nat := [360581839679872366, 360581840151299984, 360581840460041673, 360581840768871131, 360581840813494096, 360581841085144096, 360581841588269789, 360581842091525027, 360581842383595359, 360581842833643314]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 55380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 55300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360615662891347755, 360615682306666872⟩, ⟨(-1875331066707990004), (-1874604340406020908)⟩, true⟩

def words09 : List Nat := [360581843175781913, 360581843518123125, 360581843958400565, 360581844074123434, 360581844074840746, 360581843912422941, 360581843784318716, 360581844070973428, 360581844682395086, 360581845293970242]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 55390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 55300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 55300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk553
