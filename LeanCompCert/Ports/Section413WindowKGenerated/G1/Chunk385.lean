import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk385

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473578845621287, 362473599813698220⟩, ⟨443232946237777788, 443778478791975370⟩, true⟩

def state01 : KState := ⟨⟨362496169385800245, 362496190365127962⟩, ⟨(-426493282890032393), (-425947317122382629)⟩, true⟩

def words00 : List Nat := [371285126603812837, 371285126720403598, 371285127449681633, 371285128179444161, 371285128717310168, 371285128718575186, 371285128780937540, 371285128951904339, 371285129670053721, 371285129958565620]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 38500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 38500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488379046917499, 362488400037737827⟩, ⟨(-126400099411298000), (-125853691006252838)⟩, true⟩

def words01 : List Nat := [371285130111173963, 371285130264201514, 371285130908323801, 371285131318360204, 371285131933477654, 371285132549033313, 371285133083426642, 371285133084686017, 371285132806376572, 371285132892777773]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 38510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 38500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475727916083157, 362475748918135693⟩, ⟨361031697202081023, 361578538330042083⟩, true⟩

def words02 : List Nat := [371285133255959942, 371285133257231391, 371285133184698645, 371285133111735515, 371285133038308475, 371285133022302707, 371285132867621710, 371285133067415172, 371285133254707094, 371285133256010857]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 38520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 38500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493157454117026, 362493178467536668⟩, ⟨(-310611557551103079), (-310064278391119011)⟩, true⟩

def words03 : List Nat := [371285133340130735, 371285133668434144, 371285134281636681, 371285134282896544, 371285133999614193, 371285133541022343, 371285133207718272, 371285133209118838, 371285133207222722, 371285133417372139]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 38530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 38500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362469669248723016, 362469690273524595⟩, ⟨594746427352846231, 595294145230229633⟩, true⟩

def words04 : List Nat := [371285133585142647, 371285133586424591, 371285133476514776, 371285133758930355, 371285134147509092, 371285134148769384, 371285133641363810, 371285133136686627, 371285132631548140, 371285132404399569]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 38540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 38500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362460415676782917, 362460436712953550⟩, ⟨951584863795787003, 952133020006087981⟩, true⟩

def words05 : List Nat := [371285132095657938, 371285132187996755, 371285132263662890, 371285132264924037, 371285131565897137, 371285130899106644, 371285130235506083, 371285130236772666, 371285129598265130, 371285128959323003]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 38550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 38500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362501849897174776, 362501870944633987⟩, ⟨(-646340248492759825), (-645791656936172503)⟩, true⟩

def words06 : List Nat := [371285128351516608, 371285128352905074, 371285128049606009, 371285128019967589, 371285127989958147, 371285127849486419, 371285127109415273, 371285127041899439, 371285127576516385, 371285128011940094]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 38560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 38500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489097652096324, 362489118711024467⟩, ⟨(-154377078431556210), (-153828044458297430)⟩, true⟩

def words07 : List Nat := [371285128399246422, 371285128786940397, 371285129593976005, 371285130064813306, 371285130734534860, 371285131404719139, 371285131827920104, 371285131829181513, 371285131461046976, 371285131565941180]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 38570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 38500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481960394762081, 362481981464927160⟩, ⟨121026865111265946, 121576332662801890⟩, true⟩

def words08 : List Nat := [371285132172165106, 371285132173426800, 371285131964392870, 371285131745040461, 371285131525175344, 371285131510509349, 371285131445000773, 371285131690963718, 371285131925723338, 371285131927032960]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 38580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 38500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499949947196071, 362499971028800765⟩, ⟨(-573274233525494681), (-572724324462954081)⟩, true⟩

def words09 : List Nat := [371285131912495315, 371285131980261307, 371285132718184004, 371285132732504952, 371285132733482653, 371285132693804011, 371285133059745871, 371285133224375429, 371285133609638041, 371285133995447667]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 38590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 38500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 38500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk385
