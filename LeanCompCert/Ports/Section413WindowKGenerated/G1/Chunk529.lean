import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk529

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362446640733112309, 362446681352980689⟩, ⟨2026762029352159855, 2028213672535363187⟩, true⟩

def state01 : KState := ⟨⟨362486145323637083, 362486185959372604⟩, ⟨(-63209729011565565), (-61757246374129747)⟩, true⟩

def words00 : List Nat := [371285021152534500, 371285020786621468, 371285020241333899, 371285020053642293, 371285019865385863, 371285019618317413, 371285019074058247, 371285018860512840, 371285018744391149, 371285018768308853]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 52900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 52900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481851479850661, 362481892131788254⟩, ⟨164004805365581739, 165458145333167733⟩, true⟩

def words01 : List Nat := [371285018791536671, 371285018815372200, 371285018986350443, 371285018988304801, 371285019045096122, 371285019111275096, 371285019172501780, 371285019174275634, 371285018759747680, 371285018702939675]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 52910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 52900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362454395016334119, 362454435684061357⟩, ⟨1617129372259267718, 1618583547897309542⟩, true⟩

def words02 : List Nat := [371285018675604328, 371285018677378857, 371285018298953915, 371285017875754769, 371285017451911914, 371285017092703994, 371285016554403578, 371285016164687219, 371285015774374810, 371285015384569525]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 52920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 52900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362497834459840899, 362497875143592752⟩, ⟨(-682345562368137245), (-680890538465941227)⟩, true⟩

def words03 : List Nat := [371285014808046702, 371285014502410588, 371285014195873343, 371285014184261326, 371285013948724377, 371285013654861078, 371285013420850896, 371285013422829907, 371285013590077669, 371285013834995145]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 52930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 52900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472075379989464, 362472116079774790⟩, ⟨681401067339298550, 682856940135507250⟩, true⟩

def words04 : List Nat := [371285014008292118, 371285014010067078, 371285013748295349, 371285013669837811, 371285013619192601, 371285013620970098, 371285013267112881, 371285012879024778, 371285012490217224, 371285012339267435]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 52940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 52900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362467975164282812, 362468015880057928⟩, ⟨898627576151155867, 900084295689358473⟩, true⟩

def words05 : List Nat := [371285012209560488, 371285012324136883, 371285012422006331, 371285012423795273, 371285012287284247, 371285012093730661, 371285012059708599, 371285012061484013, 371285011748347409, 371285011429447833]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 52950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 52900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481013378890078, 362481054110571317⟩, ⟨208177891099122349, 209635453107060037⟩, true⟩

def words06 : List Nat := [371285011109807930, 371285011111807892, 371285011275907680, 371285011537273427, 371285011689852890, 371285011691628989, 371285011498149982, 371285011580950168, 371285011734806517, 371285011736644700]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 52960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 52900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484856791828847, 362484897539684923⟩, ⟨4613006473268009, 6071425342432727⟩, true⟩

def words07 : List Nat := [371285011663259857, 371285011590547447, 371285011798425299, 371285011917123759, 371285012090328971, 371285012264270380, 371285012437642871, 371285012439419004, 371285012138108705, 371285012138124758]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 52970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 52900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472034637720484, 362472075401410148⟩, ⟨684030747547005519, 685490005363298713⟩, true⟩

def words08 : List Nat := [371285012490808807, 371285012492585474, 371285012421578190, 371285012258278754, 371285012094289508, 371285012040220738, 371285011807497495, 371285011757764696, 371285011707445614, 371285011615891434]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 52980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 52900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494034838974989, 362494075618736224⟩, ⟨(-481874010117589737), (-480413900591058163)⟩, true⟩

def words09 : List Nat := [371285011393035235, 371285011415265643, 371285011767197301, 371285011768974066, 371285011646820637, 371285011466813608, 371285011286128910, 371285011215800534, 371285011203503132, 371285011376540963]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 52990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 52900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 52900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk529
