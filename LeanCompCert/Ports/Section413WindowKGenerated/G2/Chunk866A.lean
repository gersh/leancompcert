import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk866A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582173297778643, 360582222446944403⟩, ⟨(-5012140173161577), (-2137800711471343)⟩, true⟩

def state01 : KState := ⟨⟨360585381929444562, 360585431090468227⟩, ⟨(-282987152367555757), (-280111785951686543)⟩, true⟩

def words00 : List Nat := [360582197762418787, 360582197697248435, 360582197633087134, 360582197589888552, 360582197546336713, 360582197469368044, 360582197354089566, 360582197172270949, 360582196990217808, 360582196954088880]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 86600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 86600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577840122543503, 360577889295318391⟩, ⟨370238170224817937, 373114554472394899⟩, true⟩

def words01 : List Nat := [360582196988947868, 360582197024027515, 360582197025137414, 360582196993550124, 360582196983428400, 360582196895065999, 360582196806326066, 360582196829994406, 360582196831109704, 360582196782670878]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 86610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 86600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591070932519089, 360591120117044314⟩, ⟨(-775926140471207905), (-773048738351959497)⟩, true⟩

def words02 : List Nat := [360582196733952625, 360582196713556112, 360582196788693916, 360582196864067898, 360582196865257524, 360582196802053110, 360582196605377467, 360582196542207208, 360582196547263615, 360582196651560227]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 86620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 86600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576175135806064, 360576224332216797⟩, ⟨514608952000141605, 517487383819225171⟩, true⟩

def words03 : List Nat := [360582196674414798, 360582196697436290, 360582196799654717, 360582196969045581, 360582197104486853, 360582197240136889, 360582197308990323, 360582197310236502, 360582197245805112, 360582197178290427]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 86630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 86600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360561439655291696, 360561488863437985⟩, ⟨1791343974998873529, 1794223423645909457⟩, true⟩

def words04 : List Nat := [360582197110361355, 360582197105564309, 360582196967451059, 360582196761635131, 360582196555626885, 360582196253112588, 360582196053076110, 360582195873879914, 360582195694554931, 360582195423433899]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 86640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 86600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk866A
