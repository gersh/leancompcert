import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk056

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362532282359585743, 362532282733119841⟩, ⟨(-281586536838848136), (-281585119548964768)⟩, true⟩

def state01 : KState := ⟨⟨362279827565316614, 362279827940247406⟩, ⟨1132782891964614643, 1132784317083249813⟩, true⟩

def words00 : List Nat := [371282017566300767, 371282017566455712, 371281984218497398, 371281971370376879, 371281958526767032, 371281949474087175, 371281898228491834, 371281840334766660, 371281782461620793, 371281750278408414]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 5600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 5600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362246574831937043, 362246575208266392⟩, ⟨1320318161132622542, 1320319594104253066⟩, true⟩

def words01 : List Nat := [371281714291642356, 371281703977443060, 371281693666867880, 371281683367211318, 371281647276418952, 371281621149714074, 371281595032227665, 371281591206975956, 371281549330553597, 371281507520384587]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 5610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 5600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362249612629765565, 362249613007490919⟩, ⟨1303457619793475374, 1303459060617804962⟩, true⟩

def words02 : List Nat := [371281465725027428, 371281426924903011, 371281372417688677, 371281349292514434, 371281326175513673, 371281298050999895, 371281237518818709, 371281195930924224, 371281154357725203, 371281133266925698]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 5620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 5600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362231003510031616, 362231003889178822⟩, ⟨1408510613767681331, 1408512062604259835⟩, true⟩

def words03 : List Nat := [371281092151741528, 371281051104103427, 371281010070973141, 371280993520520538, 371280961540081909, 371280927586047763, 371280893644009413, 371280859825115794, 371280784357614656, 371280740070491635]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 5630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 5600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362285961163107176, 362285961543649554⟩, ⟨1099033839230178265, 1099035295942822779⟩, true⟩

def words04 : List Nat := [371280695798982698, 371280682685804632, 371280653610734550, 371280618400043444, 371280583201768741, 371280557901848133, 371280516975081923, 371280507140899929, 371280497310147128, 371280481065055364]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 5640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 5600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362748494542894918, 362748494924851583⟩, ⟨(-1516543057611058614), (-1516541592900401498)⟩, true⟩

def words05 : List Nat := [371280446643020396, 371280443285626758, 371280467615618610, 371280467939788323, 371280467939910203, 371280465291273218, 371280491005749018, 371280507366185348, 371280554713917281, 371280602044989297]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 5650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 5600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362510080640368458, 362510081023745799⟩, ⟨(-166735433423348674), (-166733960664614030)⟩, true⟩

def words06 : List Nat := [371280643203477340, 371280653141831858, 371280675586960804, 371280698024246562, 371280720143671353, 371280720143828494, 371280700960402871, 371280681899063239, 371280674681293386, 371280679866866129]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 5660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 5600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362349741830067323, 362349742214860886⟩, ⟨743879519825874497, 743881000621846561⟩, true⟩

def words07 : List Nat := [371280709803294381, 371280739729233491, 371280768352391659, 371280768352548969, 371280755786953289, 371280750705649004, 371280753078883762, 371280753079041653, 371280730240852683, 371280707179759099]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 5670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 5600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362359976605466171, 362359976991669972⟩, ⟨685926448084801661, 685927936898149085⟩, true⟩

def words08 : List Nat := [371280684126713585, 371280669898082046, 371280641389365907, 371280642512836235, 371280642512958161, 371280638288061086, 371280593047962439, 371280560695836886, 371280528355001047, 371280526716959630]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 5680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 5600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481509539872013, 362481509927515340⟩, ⟨(-6290466506201832), (-6288969494685772)⟩, true⟩

def words09 : List Nat := [371280505534558962, 371280478210188140, 371280454262209548, 371280454262384022, 371280447100750987, 371280441010378933, 371280434922090936, 371280428427746762, 371280406599339890, 371280406793066176]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 5690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 5600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 5600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk056
