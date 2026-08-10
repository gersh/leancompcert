import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk730A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482496986678591, 362482576332295156⟩, ⟨194232710115271357, 198144392251839811⟩, true⟩

def state01 : KState := ⟨⟨362489713229668417, 362489792597768858⟩, ⟨(-332577744103330315), (-328664420533068035)⟩, true⟩

def words00 : List Nat := [371285290711248343, 371285290742120044, 371285290850425467, 371285290959696177, 371285291046192586, 371285291048700498, 371285290907086073, 371285290863543117, 371285290959453119, 371285291023752161]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 73000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 73000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496707496597202, 362496786887481208⟩, ⟨(-843255625864658354), (-839340638746376330)⟩, true⟩

def words01 : List Nat := [371285291087758346, 371285291152587213, 371285291403849906, 371285291574314475, 371285291759181832, 371285291945022608, 371285292085004276, 371285292087529475, 371285292216657671, 371285292377152038]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 73010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 73000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483444740707603, 362483524153935445⟩, ⟨125262012860891103, 129178631640673647⟩, true⟩

def words02 : List Nat := [371285292616704935, 371285292654163140, 371285292678196228, 371285292703159958, 371285292743490831, 371285292746280860, 371285292804829858, 371285292918982093, 371285292994712644, 371285292997309958]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 73020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 73000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362511097071247932, 362511176507221769⟩, ⟨(-1894360282458837083), (-1890442002429107615)⟩, true⟩

def words03 : List Nat := [371285293029013811, 371285293086237996, 371285293319597501, 371285293391765857, 371285293430144930, 371285293469269503, 371285293694709931, 371285293864572070, 371285294220636246, 371285294577861149]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 73030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 73000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494389724916463, 362494469183488271⟩, ⟨(-674000964357814844), (-670081033654310740)⟩, true⟩

def words04 : List Nat := [371285294914296514, 371285295025785196, 371285295323774904, 371285295623057814, 371285295929301674, 371285295986533245, 371285296041456644, 371285296097243493, 371285296271195586, 371285296399629675]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 73040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 73000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk730A
