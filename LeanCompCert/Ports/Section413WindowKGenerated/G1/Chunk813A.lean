import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk813A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491279681283571, 362491378917266518⟩, ⟨(-508882104134716793), (-503434292745056821)⟩, true⟩

def state01 : KState := ⟨⟨362483303734889943, 362483402995910081⟩, ⟨139597607413283714, 145047454458423322⟩, true⟩

def words00 : List Nat := [371285186817287928, 371285186826337986, 371285186828442286, 371285186827054754, 371285186824601519, 371285186805278935, 371285186762927104, 371285186819439711, 371285186875106715, 371285186878021242]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 81300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 81300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492171048494021, 362492270335035781⟩, ⟨(-581443349931796988), (-575991427601178072)⟩, true⟩

def words01 : List Nat := [371285186931166102, 371285187007826705, 371285187172494945, 371285187175309689, 371285187156736119, 371285187124863154, 371285187192113769, 371285187219830442, 371285187308874448, 371285187399169263]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 81310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 81300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486678437645657, 362486777749590506⟩, ⟨(-134810608152352254), (-129356619915402016)⟩, true⟩

def words02 : List Nat := [371285187488453684, 371285187491268886, 371285187399739175, 371285187387048766, 371285187401243822, 371285187404109477, 371285187326846182, 371285187250697087, 371285187230949162, 371285187253716665]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 81320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 81300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485139215482906, 362485238552760307⟩, ⟨(-9562680497344195), (-4106631831711947)⟩, true⟩

def words03 : List Nat := [371285187426302991, 371285187600005618, 371285187742836872, 371285187750967146, 371285187804725055, 371285187859899544, 371285188049102675, 371285188059601400, 371285188062331155, 371285188066144312]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 81330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 81300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488915877975019, 362489015240440376⟩, ⟨(-316744201194162282), (-311286103612836946)⟩, true⟩

def words04 : List Nat := [371285188168832820, 371285188197519454, 371285188376060816, 371285188555788144, 371285188670078046, 371285188672894043, 371285188603552365, 371285188598098367, 371285188733482414, 371285188783437846]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 81340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 81300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk813A
