import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk253

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360461577828897025, 360461581622368649⟩, ⟨3088605458207842110, 3088670383218490182⟩, true⟩

def state01 : KState := ⟨⟨360572230379701470, 360572234176289411⟩, ⟨288589890289946232, 288654894159359192⟩, true⟩

def words00 : List Nat := [360583658630786799, 360583655364017939, 360583652878888587, 360583651951559903, 360583651024283976, 360583648607575078, 360583644636391357, 360583642222727246, 360583639809153192, 360583638952826723]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360484238415841420, 360484242215582987⟩, ⟨2516188439444801275, 2516253523148293223⟩, true⟩

def words01 : List Nat := [360583638502539087, 360583636657016397, 360583634811571532, 360583633473668880, 360583632915813240, 360583631683435958, 360583630451123012, 360583628122730084, 360583624241476753, 360583620316813173]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360518384350980516, 360518388153841186⟩, ⟨1651456561589368656, 1651521724283752054⟩, true⟩

def words02 : List Nat := [360583616392350516, 360583614023691700, 360583611440369333, 360583607844865074, 360583604249589776, 360583600235948979, 360583597546782643, 360583594752819782, 360583591959041572, 360583588379829491]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360539846792292301, 360539850598280997⟩, ⟨1107484064308021051, 1107549306250710335⟩, true⟩

def words03 : List Nat := [360583585806167301, 360583584306726510, 360583582807314099, 360583580370702098, 360583576972770468, 360583572217954202, 360583567463451402, 360583563150537472, 360583559872420487, 360583558147856795]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360545978465740551, 360545982274884645⟩, ⟨951695039904558110, 951760361820306788⟩, true⟩

def words04 : List Nat := [360583556423375913, 360583553914791033, 360583549856144312, 360583547350674802, 360583544845310160, 360583541522665443, 360583538604110677, 360583534239123331, 360583529874417226, 360583527062333178]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360522810388204631, 360522814200466620⟩, ⟨1539268581854346916, 1539333982824646468⟩, true⟩

def words05 : List Nat := [360583525581603134, 360583525172550027, 360583524763496152, 360583523550556255, 360583522387268837, 360583520203546311, 360583518019899384, 360583517387770387, 360583515883266672, 360583513490010179]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 25350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 25300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593779147169021, 360593782962566810⟩, ⟨(-261028080854107030), (-260962600344459818)⟩, true⟩

def words06 : List Nat := [360583511096872386, 360583508661990059, 360583507035528601, 360583505850714767, 360583504665968396, 360583502171900155, 360583499461329107, 360583498301053778, 360583497140767392, 360583497100742505]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 25360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 25300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360555094069331402, 360555097887889504⟩, ⟨720712855120087730, 720778415822398290⟩, true⟩

def words07 : List Nat := [360583497101040859, 360583496732908446, 360583497545587105, 360583499503541151, 360583500220935455, 360583500938323425, 360583500938621074, 360583500477769093, 360583498471290416, 360583497352657921]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 25370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 25300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573496520617917, 360573500342306313⟩, ⟨253610047908464456, 253675688073383686⟩, true⟩

def words08 : List Nat := [360583496234001062, 360583495623187611, 360583495415333395, 360583494425749707, 360583493436189387, 360583492050979143, 360583491872842091, 360583492304650398, 360583492304955653, 360583491507649889]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 25380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 25300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360629632646270937, 360629636471091705⟩, ⟨(-1171960900224464000), (-1171895180513062764)⟩, true⟩

def words09 : List Nat := [360583492267678917, 360583493421206825, 360583495616545647, 360583496268264241, 360583496268570408, 360583495607467522, 360583495458174980, 360583497048432539, 360583498865215766, 360583500681929347]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 25390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 25300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 25300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk253
