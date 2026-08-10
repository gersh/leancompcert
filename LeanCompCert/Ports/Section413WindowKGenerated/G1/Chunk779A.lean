import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk779A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362503665282644109, 362503756093560528⟩, ⟨(-1448359631548610426), (-1443582565568870776)⟩, true⟩

def state01 : KState := ⟨⟨362488292010727741, 362488382845934642⟩, ⟨(-250739563793658082), (-245960605462936518)⟩, true⟩

def words00 : List Nat := [371285225334221857, 371285225416381086, 371285225553224800, 371285225691492298, 371285225878761387, 371285225881449468, 371285225849290093, 371285225818016139, 371285225859043886, 371285225902685770]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 77900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 77900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362469732761382125, 362469823620783498⟩, ⟨1195357081184607430, 1200137924632704574⟩, true⟩

def words01 : List Nat := [371285226049220808, 371285226196865143, 371285226312087668, 371285226314775953, 371285226226808152, 371285226190559588, 371285226181947703, 371285226184636083, 371285225996150555, 371285225801541105]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 77910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 77900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484752846520065, 362484843730001170⟩, ⟨24945627383734331, 29728347242372831⟩, true⟩

def words02 : List Nat := [371285225605700802, 371285225551559000, 371285225440765885, 371285225448651350, 371285225450734421, 371285225433448453, 371285225225477668, 371285225164425892, 371285225202224127, 371285225205007489]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 77920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 77900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492226000137997, 362492316908138026⟩, ⟨(-557484425973034137), (-552699795228730411)⟩, true⟩

def words03 : List Nat := [371285225202176709, 371285225168299875, 371285225261149224, 371285225320834327, 371285225381166810, 371285225442541137, 371285225503434538, 371285225506176411, 371285225555111137, 371285225649426582]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 77930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 77900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479874766868637, 362479965698800083⟩, ⟨405244734947045850, 410031231032670682⟩, true⟩

def words04 : List Nat := [371285225867766986, 371285225870456161, 371285225869649348, 371285225869809111, 371285225868953294, 371285225847542893, 371285225802395873, 371285225840144138, 371285225878578677, 371285225881366250]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 77940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 77900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk779A
