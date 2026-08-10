import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk600A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496051130465483, 362496103914161724⟩, ⟨(-658473698172781565), (-656334432942814035)⟩, true⟩

def state01 : KState := ⟨⟨362487394560028772, 362487447361807209⟩, ⟨(-139016760885907356), (-136876410630361474)⟩, true⟩

def words00 : List Nat := [371285165577953889, 371285165681530371, 371285165769428427, 371285165858013890, 371285165960619835, 371285165962857917, 371285166116476875, 371285166292914486, 371285166466337573, 371285166506453518]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362513423333819910, 362513476153956877⟩, ⟨(-1701163994844176803), (-1699022542798971593)⟩, true⟩

def words01 : List Nat := [371285166659146715, 371285166812863213, 371285167243565969, 371285167352887780, 371285167419013993, 371285167485813527, 371285167829769296, 371285168072160562, 371285168545183343, 371285169019074104]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362493712452538032, 362493765291008459⟩, ⟨(-518077789165370549), (-515935236655540287)⟩, true⟩

def words02 : List Nat := [371285169485698638, 371285169582670188, 371285169936375166, 371285170291140057, 371285170658616136, 371285170660647788, 371285170658122803, 371285170568903965, 371285170665365043, 371285170810878934]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495793028712169, 362495845885520671⟩, ⟨(-642917801559586530), (-640774148122079486)⟩, true⟩

def words03 : List Nat := [371285171201260365, 371285171592523160, 371285171982121163, 371285172107511714, 371285172315795820, 371285172525054968, 371285173011079179, 371285173249730063, 371285173429048880, 371285173609107519]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362505502406522810, 362505555281526033⟩, ⟨(-1225822942550857228), (-1223678196609560756)⟩, true⟩

def words04 : List Nat := [371285174066013181, 371285174385583419, 371285174936050524, 371285175487313121, 371285175995231934, 371285176274176721, 371285176689937270, 371285177106781717, 371285177624189131, 371285177965634382]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk600A
