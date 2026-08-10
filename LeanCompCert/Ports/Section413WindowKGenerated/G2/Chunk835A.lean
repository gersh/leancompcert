import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk835A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588789735139819, 360588835299817973⟩, ⟨(-536549375361945931), (-533979932483093117)⟩, true⟩

def state01 : KState := ⟨⟨360599326552753714, 360599372128750939⟩, ⟨(-1416477683173479683), (-1413907295096161963)⟩, true⟩

def words00 : List Nat := [360582440507027762, 360582440679599579, 360582440821146420, 360582440962905710, 360582440988031355, 360582440989229796, 360582440975989310, 360582441028786194, 360582441133654944, 360582441337656399]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587697376933901, 360587742964348073⟩, ⟨(-445248779072469594), (-442677437510164698)⟩, true⟩

def words01 : List Nat := [360582441469042794, 360582441600559651, 360582441799391385, 360582442079357633, 360582442323017380, 360582442566866823, 360582442675829267, 360582442677027459, 360582442706292012, 360582442771133072]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575986868848365, 360576032467543266⟩, ⟨532817969876821745, 535390253662974857⟩, true⟩

def words02 : List Nat := [360582442885432717, 360582442886630934, 360582442857998930, 360582442720437157, 360582442582665635, 360582442364021392, 360582442216656470, 360582442176449398, 360582442136122303, 360582442024033904]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360604901627582244, 360604947237609826⟩, ⟨(-1882656071384993361), (-1880082840926143627)⟩, true⟩

def words03 : List Nat := [360582441948286808, 360582441869121376, 360582441818644891, 360582441826933717, 360582441828038947, 360582441714316452, 360582441628620487, 360582441784761468, 360582442055127570, 360582442325759045]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579631873912548, 360579677495341248⟩, ⟨228418791408349620, 230992974372919550⟩, true⟩

def words04 : List Nat := [360582442524438377, 360582442580290008, 360582442699062101, 360582442818181537, 360582442819209986, 360582442807722092, 360582442713039993, 360582442546616291, 360582442379968306, 360582442222742480]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk835A
