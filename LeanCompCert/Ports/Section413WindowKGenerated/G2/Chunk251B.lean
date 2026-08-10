import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk251A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk251B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk251A

def state06 : KState := ⟨⟨360611950491189340, 360611954240969532⟩, ⟨(-707992043342666313), (-707928220667259273)⟩, true⟩

def words05 : List Nat := [360583819865738074, 360583819650954347, 360583820797336539, 360583820797665222, 360583820586598961, 360583819030703252, 360583817474869663, 360583816147732630, 360583817188932504, 360583818307554038]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 25150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 25100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601344565954465, 360601348318863807⟩, ⟨(-441394311241487864), (-441330409820870440)⟩, true⟩

def words06 : List Nat := [360583818629639222, 360583818629968446, 360583819512334465, 360583820741114098, 360583820878923440, 360583820879252276, 360583819445877553, 360583817216850389, 360583814987933975, 360583815030165668]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 25160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 25100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360514931539200658, 360514935295210889⟩, ⟨1734390537717297737, 1734454517202734587⟩, true⟩

def words07 : List Nat := [360583817301114244, 360583819571951276, 360583821058426223, 360583821702793209, 360583821703069560, 360583821481275390, 360583821543931585, 360583821544260518, 360583820259213870, 360583817523852777]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 25170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 25100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360644432605364636, 360644436364480094⟩, ⟨(-1527279954333674739), (-1527215896643298883)⟩, true⟩

def words08 : List Nat := [360583814788636049, 360583812341662208, 360583810711562827, 360583810654231340, 360583810596879288, 360583809068270912, 360583807667763111, 360583807421403371, 360583808500038699, 360583810907108680]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 25180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 25100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360609693221613468, 360609696983871697⟩, ⟨(-652089365905828298), (-652025229034271980)⟩, true⟩

def words09 : List Nat := [360583812493920456, 360583814080639280, 360583815142789644, 360583817443002422, 360583819341873281, 360583821240647014, 360583822062326929, 360583822062656401, 360583822966461095, 360583823993552493]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 25190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 25100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 25100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk251B
