import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk869A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585152505848762, 360585202009334097⟩, ⟨(-265218429443054363), (-262313352758273647)⟩, true⟩

def state01 : KState := ⟨⟨360569306704915156, 360569356220296547⟩, ⟨1111741172330447420, 1114647282841360970⟩, true⟩

def words00 : List Nat := [360582183479559406, 360582183441617415, 360582183271110846, 360582183153934387, 360582183036435584, 360582182805615554, 360582182517533206, 360582182150500084, 360582181783235735, 360582181525587554]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 86900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 86900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360541515561083393, 360541565088256144⟩, ⟨3527220319874597680, 3530127455232182172⟩, true⟩

def words01 : List Nat := [360582181379037039, 360582181253310661, 360582181127441973, 360582180903771843, 360582180547608770, 360582180158470328, 360582179768974990, 360582179442355672, 360582179077632606, 360582178611671149]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 86910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 86900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582245208100815, 360582294747076536⟩, ⟨(-13224348510329692), (-10316187180256070)⟩, true⟩

def words02 : List Nat := [360582178145438495, 360582177724594092, 360582177404859407, 360582177217550394, 360582177030151566, 360582176729279905, 360582176433303682, 360582176269870117, 360582176106072969, 360582176076094030]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 86920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 86900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573914004311930, 360573963555229269⟩, ⟨710989918898154357, 713899118370057617⟩, true⟩

def words03 : List Nat := [360582176077224116, 360582175996281569, 360582175915125735, 360582175766930423, 360582175685053208, 360582175570081910, 360582175454976752, 360582175273817615, 360582175048237729, 360582174955256530]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 86930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 86900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575220683709637, 360575270246401865⟩, ⟨597369567241747572, 600279790481273460⟩, true⟩

def words04 : List Nat := [360582174873765233, 360582174875017287, 360582174817367282, 360582174686731765, 360582174555877965, 360582174392082297, 360582174308421466, 360582174221593973, 360582174134642391, 360582173981772553]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 86940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 86900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk869A
