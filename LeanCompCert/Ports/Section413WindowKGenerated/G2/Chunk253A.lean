import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk253A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk253A
