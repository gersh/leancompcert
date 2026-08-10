import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk727A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482472303601456, 362482550973036076⟩, ⟨194625125306069900, 198487547458905998⟩, true⟩

def state01 : KState := ⟨⟨362485143403918253, 362485222095733584⟩, ⟨487261002268715, 4351310344901991⟩, true⟩

def words00 : List Nat := [371285281316205659, 371285281400972135, 371285281571370927, 371285281742813143, 371285281867162968, 371285281869659171, 371285281801137693, 371285281863462742, 371285281937862247, 371285281940463950]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 72700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 72700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486626420213977, 362486705134797989⟩, ⟨(-107348701699279488), (-103482996733609648)⟩, true⟩

def words01 : List Nat := [371285281941526442, 371285281943434986, 371285282043698855, 371285282050960815, 371285282114610760, 371285282179241054, 371285282243691003, 371285282246187925, 371285282098132626, 371285282120857950]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 72710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 72700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485038549945179, 362485117286790242⟩, ⟨8115280026136889, 11982603932445437⟩, true⟩

def words02 : List Nat := [371285282233748464, 371285282236257202, 371285282168470850, 371285282062132595, 371285281954865600, 371285281907481757, 371285281877827846, 371285281959312863, 371285282038785929, 371285282041416015]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 72720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 72700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362506913652329613, 362506992411720654⟩, ⟨(-1582955476003670387), (-1579086512215137049)⟩, true⟩

def words03 : List Nat := [371285282214434563, 371285282391010020, 371285282755105251, 371285282899950929, 371285283025282192, 371285283151413982, 371285283355828830, 371285283468267651, 371285283768407471, 371285284069627266]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 72730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 72700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485139456338792, 362485218238258253⟩, ⟨965120305144053, 4835722925782951⟩, true⟩

def words04 : List Nat := [371285284370592549, 371285284454296498, 371285284580568653, 371285284708190679, 371285284891853414, 371285284894351408, 371285284826419338, 371285284742801890, 371285284705823546, 371285284708676477]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 72740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 72700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk727A
