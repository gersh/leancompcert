import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk554A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362505925973688736, 362505970689324783⟩, ⟨(-1166481219211323254), (-1164807747339207928)⟩, true⟩

def state01 : KState := ⟨⟨362482411403417518, 362482456135869301⟩, ⟨136274436853231853, 137948840402631937⟩, true⟩

def words00 : List Nat := [371284946015445072, 371284946017309526, 371284946066120959, 371284946193943619, 371284946337104443, 371284946338977868, 371284946169742822, 371284945934284174, 371284945735626840, 371284945737753485]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 55400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 55400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479678322154552, 362479723071395722⟩, ⟨287805881168980976, 289481215104211030⟩, true⟩

def words01 : List Nat := [371284945974419289, 371284946256780520, 371284946522383101, 371284946524248182, 371284946395741582, 371284946367565666, 371284946594618028, 371284946596495778, 371284946570551209, 371284946478380642]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 55410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 55400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362499726617033355, 362499771382963356⟩, ⟨(-823316627490401519), (-821640368574680067)⟩, true⟩

def words02 : List Nat := [371284946579693203, 371284946613935554, 371284946889230595, 371284947165297729, 371284947389554655, 371284947391453457, 371284947654203738, 371284947920968693, 371284948354355060, 371284948623702750]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 55420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 55400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498094371908949, 362498139154905418⟩, ⟨(-732832611447401916), (-731155406457743832)⟩, true⟩

def words03 : List Nat := [371284948889621130, 371284949156171850, 371284949556919938, 371284949795387199, 371284950132606247, 371284950470510121, 371284950769627126, 371284950771493405, 371284950923658677, 371284951163951833]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 55430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 55400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484639998122349, 362484684797703508⟩, ⟨13220924989288288, 14899049521793938⟩, true⟩

def words04 : List Nat := [371284951727947965, 371284951954837335, 371284952181866075, 371284952409499308, 371284952693599133, 371284952815474507, 371284953051214467, 371284953287700461, 371284953489178657, 371284953491112378]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 55440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 55400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk554A
