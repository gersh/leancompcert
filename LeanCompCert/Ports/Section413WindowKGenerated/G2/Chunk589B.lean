import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk589A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk589B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk589A

def state06 : KState := ⟨⟨360537090539261310, 360537112640243102⟩, ⟨2647270618422658288, 2648150963941578612⟩, true⟩

def words05 : List Nat := [360582030601017226, 360582030468909562, 360582030336716670, 360582030035144855, 360582029740609806, 360582029287815983, 360582028834795395, 360582028383280765, 360582027766234515, 360582027005303170]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566505341671025, 360566527450433613⟩, ⟨912795058162169031, 913675862475457713⟩, true⟩

def words06 : List Nat := [360582026244216641, 360582025474932407, 360582024867498213, 360582024547957633, 360582024228363580, 360582023666057687, 360582022816824209, 360582022255582865, 360582021694089183, 360582021360260228]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360554651934790249, 360554674051391217⟩, ⟨1611795617350401094, 1612676883932443186⟩, true⟩

def words07 : List Nat := [360582021098261229, 360582020620823939, 360582020143245551, 360582019761279815, 360582019522329240, 360582019076113764, 360582018629828388, 360582018039831878, 360582017289298146, 360582016826635918]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571406038530845, 360571428162902637⟩, ⟨623547277241473646, 624429002185051974⟩, true⟩

def words08 : List Nat := [360582016363718967, 360582015969274757, 360582015728961314, 360582015343894494, 360582014958706230, 360582014454233309, 360582014122761498, 360582013990490576, 360582013858146970, 360582013499437390]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360601068489874733, 360601090622024435⟩, ⟨(-1126429727545644697), (-1125547543745811581)⟩, true⟩

def words09 : List Nat := [360582013428686086, 360582013537612894, 360582013606340931, 360582013607169032, 360582013593119057, 360582013320645257, 360582013062129563, 360582013220145252, 360582013544157501, 360582013868346603]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk589B
