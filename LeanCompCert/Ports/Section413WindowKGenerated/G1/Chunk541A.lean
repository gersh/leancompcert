import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk541A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472808668666897, 362472851229079772⟩, ⟨653860540545953758, 655416007726125550⟩, true⟩

def state01 : KState := ⟨⟨362484760471258169, 362484803047941926⟩, ⟨7254988209329953, 8811335728112205⟩, true⟩

def words00 : List Nat := [371284966022135490, 371284966024137318, 371284966053512118, 371284966116870388, 371284966124406818, 371284966126232155, 371284965806419954, 371284965776571051, 371284965887199059, 371284965889112285]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 54100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 54100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474479378875419, 362474521972128448⟩, ⟨563681395174007633, 565238639336770827⟩, true⟩

def words01 : List Nat := [371284965887465299, 371284965845334300, 371284966049212927, 371284966161615741, 371284966351721501, 371284966542498763, 371284966665700413, 371284966667517670, 371284966335767792, 371284966145065196]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 54110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 54100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471357716608802, 362471400326036663⟩, ⟨732672601570177864, 734230721199839560⟩, true⟩

def words02 : List Nat := [371284966101301332, 371284966103118680, 371284965797712087, 371284965493144634, 371284965187877541, 371284964983202744, 371284964631207496, 371284964599869735, 371284964567891341, 371284964536662931]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 54120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 54100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488217099707747, 362488259725558883⟩, ⟨(-180086875978624262), (-178527867272680742)⟩, true⟩

def words03 : List Nat := [371284964287348636, 371284964021058964, 371284963826184591, 371284963828002355, 371284963447237019, 371284963010951172, 371284962573926890, 371284962418692571, 371284962201050604, 371284962263981286]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 54130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 54100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476640725523856, 362476683367783759⟩, ⟨446679515888468821, 448239413045047583⟩, true⟩

def words04 : List Nat := [371284962326529467, 371284962328362582, 371284962245791520, 371284962332876186, 371284962387431607, 371284962389249810, 371284961989548092, 371284961590801181, 371284961191346753, 371284961103943410]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 54140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 54100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk541A
