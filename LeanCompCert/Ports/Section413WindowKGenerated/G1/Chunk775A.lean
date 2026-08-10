import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk775A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468570031917014, 362468659876941780⟩, ⟨1277509989723964802, 1282212005688743882⟩, true⟩

def state01 : KState := ⟨⟨362485170361620348, 362485260230590349⟩, ⟨(-9105452465914791), (-4401580624039665)⟩, true⟩

def words00 : List Nat := [371285204336323144, 371285204248877419, 371285204077023789, 371285203973380654, 371285203868818301, 371285203738088409, 371285203507626573, 371285203431365605, 371285203440557095, 371285203444061676]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 77500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 77500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484237504493525, 362484327397884850⟩, ⟨63223606291209299, 67929371148442903⟩, true⟩

def words01 : List Nat := [371285203446095340, 371285203417164869, 371285203521550649, 371285203575682376, 371285203655716645, 371285203736747769, 371285203774997545, 371285203777719108, 371285203687700359, 371285203679762410]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 77510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 77500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480783862346161, 362480873779518482⟩, ⟨330994196904420072, 335701805389691128⟩, true⟩

def words02 : List Nat := [371285203825229933, 371285203827904300, 371285203784854053, 371285203742752036, 371285203699686325, 371285203668055323, 371285203622191630, 371285203684418037, 371285203736835013, 371285203739603478]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 77520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 77500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479587022836978, 362479676964197710⟩, ⟨423819623068087614, 428529107002814158⟩, true⟩

def words03 : List Nat := [371285203717495433, 371285203752660418, 371285203904447689, 371285203907122266, 371285203837568107, 371285203743807346, 371285203657606804, 371285203660554178, 371285203587909107, 371285203519614306]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 77530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 77500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482506299901181, 362482596265389992⟩, ⟨197383378380138007, 202094733327664953⟩, true⟩

def words04 : List Nat := [371285203450341079, 371285203381809757, 371285203108921014, 371285203003655194, 371285202897021367, 371285202822497344, 371285202639353203, 371285202457164308, 371285202273915775, 371285202258082806]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 77540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 77500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk775A
