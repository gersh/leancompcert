import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk966A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491408258132184, 362491550236385019⟩, ⟨(-613427148956262094), (-604167301913982568)⟩, true⟩

def state01 : KState := ⟨⟨362486341875463245, 362486483883871574⟩, ⟨(-123945812598983630), (-114683052375257506)⟩, true⟩

def words00 : List Nat := [371285296155570133, 371285296235134278, 371285296313721755, 371285296393410513, 371285296501411455, 371285296557547679, 371285296640674507, 371285296725186604, 371285296808089560, 371285296823884873]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 96600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 96600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362503083891258415, 362503225930237138⟩, ⟨(-1741488067827278749), (-1732222354040861721)⟩, true⟩

def words01 : List Nat := [371285296905860216, 371285296989550313, 371285297126197835, 371285297186788892, 371285297240379237, 371285297295042495, 371285297444486726, 371285297542022424, 371285297729876075, 371285297919203917]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 96610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 96600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487912188490117, 362488054258114394⟩, ⟨(-275562091304590344), (-266293416396393308)⟩, true⟩

def words02 : List Nat := [371285298082302186, 371285298103381183, 371285298200060101, 371285298298606219, 371285298426901302, 371285298430290612, 371285298415921716, 371285298405335735, 371285298449462154, 371285298481848016]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 96620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 96600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479663561986068, 362479805662113634⟩, ⟨521588914380407173, 530860536977844383⟩, true⟩

def words03 : List Nat := [371285298605126102, 371285298729813729, 371285298853516774, 371285298867164200, 371285298869601490, 371285298868341148, 371285298941704951, 371285298945094850, 371285298891182774, 371285298838199912]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 96630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 96600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493687812181072, 362493829942698020⟩, ⟨(-833733251661593631), (-824458692080532301)⟩, true⟩

def words04 : List Nat := [371285298824500927, 371285298840425173, 371285298961978580, 371285299084881804, 371285299176855275, 371285299196003847, 371285299310396762, 371285299426577113, 371285299585411938, 371285299677185191]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 96640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 96600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk966A
