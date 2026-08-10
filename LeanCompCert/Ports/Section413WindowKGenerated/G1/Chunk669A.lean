import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk669A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487900818989957, 362487967005868818⟩, ⟨(-167580770083454798), (-164590170982118204)⟩, true⟩

def state01 : KState := ⟨⟨362487211123446421, 362487277330642629⟩, ⟨(-121395839191478861), (-118403880754067553)⟩, true⟩

def words00 : List Nat := [371285507038153104, 371285507075876685, 371285507096548429, 371285507118008902, 371285507206972764, 371285507216781710, 371285507387109049, 371285507558337946, 371285507729105451, 371285507757915364]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 66900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 66900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498439046790625, 362498505274673538⟩, ⟨(-872759124399101861), (-869765781712004751)⟩, true⟩

def words01 : List Nat := [371285507933829177, 371285508110955227, 371285508310675675, 371285508312958472, 371285508215418892, 371285508082267844, 371285508004740191, 371285508007261167, 371285508174289100, 371285508371134858]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 66910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 66900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480341137446953, 362480407385928021⟩, ⟨338425886046996637, 341420607264899411⟩, true⟩

def words02 : List Nat := [371285508567395947, 371285508569678995, 371285508588508299, 371285508711376812, 371285508899401232, 371285508901684473, 371285508820706968, 371285508695061773, 371285508568466167, 371285508545456856]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 66920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 66900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362467736404587484, 362467802673589034⟩, ⟨1182212607962237755, 1185208702723739911⟩, true⟩

def words03 : List Nat := [371285508617481698, 371285508766627741, 371285508878686606, 371285508881010654, 371285508810676580, 371285508750254088, 371285508727645716, 371285508729929397, 371285508473383611, 371285508211424764]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 66930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 66900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491501083081389, 362491567372565572⟩, ⟨(-408735394338004726), (-405737928365256704)⟩, true⟩

def words04 : List Nat := [371285507948506639, 371285507760532972, 371285507460852702, 371285507384991141, 371285507308388183, 371285507196811445, 371285506939258852, 371285506905747989, 371285507057590082, 371285507150487258]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 66940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 66900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk669A
