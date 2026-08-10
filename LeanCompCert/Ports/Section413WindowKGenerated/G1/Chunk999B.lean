import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk999A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk999B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk999A

def state06 : KState := ⟨⟨362489844515594092, 362489996941154208⟩, ⟨(-473488695331218174), (-463201977794269716)⟩, true⟩

def words05 : List Nat := [371285362604263171, 371285362668735978, 371285362767164328, 371285362817666457, 371285362896986641, 371285362977621061, 371285363038228718, 371285363041751503, 371285363063348620, 371285363114183747]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483850395905123, 362484002852747669⟩, ⟨125731910167127252, 136021754858627312⟩, true⟩

def words06 : List Nat := [371285363263035170, 371285363288091535, 371285363304099541, 371285363321237119, 371285363367328941, 371285363371203463, 371285363402190865, 371285363440988995, 371285363474826767, 371285363478483977]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500660691726909, 362500813180290647⟩, ⟨(-1554843222536770342), (-1544550206513911982)⟩, true⟩

def words07 : List Nat := [371285363553740978, 371285363644431992, 371285363825400118, 371285363936066401, 371285364036474120, 371285364138000453, 371285364301545597, 371285364427670549, 371285364584589577, 371285364743022427]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489929525025903, 362490082045387032⟩, ⟨(-481945156775714549), (-471648961487610043)⟩, true⟩

def words08 : List Nat := [371285364878431637, 371285364881947854, 371285364949334652, 371285365019228381, 371285365117605438, 371285365121121737, 371285365086320968, 371285365052635826, 371285365079998489, 371285365131249884]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483713919911280, 362483866467923498⟩, ⟨139641172505086854, 149940132753271414⟩, true⟩

def words09 : List Nat := [371285365280852455, 371285365431919250, 371285365581657124, 371285365635280184, 371285365693896880, 371285365754191899, 371285365883981791, 371285365887498373, 371285365884245194]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99990 9 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99900 99 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 99 = 90 + 9 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99900 99 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk999B
