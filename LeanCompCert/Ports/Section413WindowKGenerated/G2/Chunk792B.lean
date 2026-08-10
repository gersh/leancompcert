import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk792A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk792B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk792A

def state06 : KState := ⟨⟨360585155131457344, 360585196020159857⟩, ⟨(-239260378809238103), (-237071559137348029)⟩, true⟩

def words05 : List Nat := [360582204972978877, 360582204888822479, 360582204813586802, 360582204977642384, 360582205030891237, 360582205084316918, 360582205085326901, 360582205039586627, 360582204957056984, 360582204996085756]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 79250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 79200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360569034976276234, 360569075875656364⟩, ⟨1038410345477676102, 1040600011512056854⟩, true⟩

def words06 : List Nat := [360582204997021995, 360582204952685545, 360582204749366317, 360582204466022936, 360582204182502202, 360582203839484075, 360582203617525668, 360582203492342600, 360582203367017063, 360582203162290804]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 79260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 79200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360591442569194532, 360591483479263741⟩, ⟨(-737988672965944698), (-735798159555140314)⟩, true⟩

def words07 : List Nat := [360582202997608947, 360582202887263095, 360582202823831818, 360582202825589575, 360582202826653787, 360582202674867848, 360582202522875030, 360582202395826833, 360582202472042221, 360582202590279557]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 79270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 79200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583507683195081, 360583548604080762⟩, ⟨(-108895596785864607), (-106704225792748577)⟩, true⟩

def words08 : List Nat := [360582202605824132, 360582202629312244, 360582202811385441, 360582202993786568, 360582203106954451, 360582203136296651, 360582203137313116, 360582203056295392, 360582202975068043, 360582202874732000]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 79280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 79200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360567349087862891, 360567390019417730⟩, ⟨1172449776430872414, 1174641993434042160⟩, true⟩

def words09 : List Nat := [360582202985667415, 360582203096816982, 360582203128346484, 360582203129479983, 360582203069375632, 360582202969969636, 360582202901273984, 360582202902407926, 360582202840510689, 360582202654896092]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 79290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 79200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 79200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk792B
