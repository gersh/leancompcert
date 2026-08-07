import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk341

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480841175082330, 362480857460412055⟩, ⟨133531239906197067, 133906564184113191⟩, true⟩

def state01 : KState := ⟨⟨362458085631318203, 362458101926614354⟩, ⟨909567292125163949, 909942956308463293⟩, true⟩

def words00 : List Nat := [371284784224807360, 371284784101779666, 371284783165435637, 371284782958459563, 371284782750918984, 371284782726531116, 371284781556483412, 371284780385145694, 371284779213439460, 371284778647702260]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 34100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 34100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362433988809949816, 362434005115213542⟩, ⟨1731650807335179237, 1732026811563848355⟩, true⟩

def words01 : List Nat := [371284777866414281, 371284777196858899, 371284776526948984, 371284775842013964, 371284774174659443, 371284772769930903, 371284771364726123, 371284770739139694, 371284769403993820, 371284767917428192]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 34110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 34100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479997666244259, 362480013981401133⟩, ⟨161680718236717322, 162057060068812306⟩, true⟩

def words02 : List Nat := [371284766430449552, 371284765658409282, 371284764635874818, 371284764472367199, 371284764308553177, 371284764012952647, 371284762703625277, 371284762253381845, 371284762209383127, 371284762210527088]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 34120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 34100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362467739565709859, 362467755890933581⟩, ⟨580145095504651212, 580521780969699724⟩, true⟩

def words03 : List Nat := [371284762072236610, 371284761932583429, 371284761895007282, 371284761896224807, 371284761572402757, 371284761510624872, 371284761448472888, 371284761387654048, 371284760540592148, 371284760043861809]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 34130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 34100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471611249318552, 362471627584392107⟩, ⟨448003110823334830, 448380132612862256⟩, true⟩

def words04 : List Nat := [371284759906380732, 371284759907486982, 371284759283551252, 371284758617854306, 371284757951750283, 371284757547784158, 371284757000094883, 371284757155889942, 371284757308944924, 371284757310090874]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 34140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 34100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478896268745482, 362478912613838610⟩, ⟨199062963407041542, 199440327414988658⟩, true⟩

def words05 : List Nat := [371284756926384845, 371284756910440101, 371284756893930979, 371284756890439102, 371284755744482859, 371284754286627002, 371284752828417594, 371284752227910317, 371284751200557887, 371284751030917504]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 34150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 34100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478532282329076, 362478548637399939⟩, ⟨211446858348879332, 211824563246690572⟩, true⟩

def words06 : List Nat := [371284750860836059, 371284750644449658, 371284749822021857, 371284749744053121, 371284749847869008, 371284749848982893, 371284749269330484, 371284748533879186, 371284747798012491, 371284747775920475]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 34160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 34100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469084136154926, 362469100501177057⟩, ⟨534507566976084190, 534885611960405722⟩, true⟩

def words07 : List Nat := [371284748270374453, 371284748946643296, 371284749624370333, 371284749625496354, 371284749813833375, 371284750032932356, 371284750492554591, 371284750493663194, 371284750039485213, 371284749582861095]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 34170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 34100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479932377189189, 362479948752138335⟩, ⟨163668088645519191, 164046472985217691⟩, true⟩

def words08 : List Nat := [371284749125797591, 371284748887118493, 371284748434989245, 371284748637806099, 371284748714858605, 371284748715965902, 371284747652719820, 371284747123745704, 371284746834431627, 371284746835583355]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 34180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 34100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362466077928875099, 362466094313925458⟩, ⟨637504618200098791, 637883347950335861⟩, true⟩

def words09 : List Nat := [371284746696088306, 371284746484778232, 371284746779502174, 371284746906097083, 371284747069652006, 371284747233597490, 371284747394827712, 371284747395935680, 371284746417792289, 371284745873807047]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 34190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 34100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 34100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk341
