import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk061

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362279441146856238, 362279441593612408⟩, ⟨1215364664158866568, 1215366510090903834⟩, true⟩

def state01 : KState := ⟨⟨362415189357620856, 362415189805902646⟩, ⟨387016429707110263, 387018284953261333⟩, true⟩

def words00 : List Nat := [371278649348209695, 371278643476915795, 371278625385075299, 371278623475049869, 371278621565593811, 371278609815363234, 371278569085476046, 371278550480006383, 371278531880542393, 371278531587400725]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 6100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 6100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362527776131733631, 362527776581577245⟩, ⟨(-301590842512045289), (-301588977715412717)⟩, true⟩

def words01 : List Nat := [371278521222324628, 371278503311767699, 371278494157678431, 371278494157866348, 371278493208055738, 371278496731000810, 371278500132840911, 371278500133015396, 371278497336637600, 371278505387701177]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 6110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 6100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362362769185079428, 362362769636446381⟩, ⟨709536251307611406, 709538125435136070⟩, true⟩

def words02 : List Nat := [371278540002391899, 371278540002563070, 371278539201818128, 371278537468806332, 371278535736299097, 371278535321817535, 371278521732644587, 371278521006424573, 371278520280383305, 371278518107153582]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 6120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 6100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362532520516827916, 362532520969745400⟩, ⟨(-331387543218768826), (-331385659578617974)⟩, true⟩

def words03 : List Nat := [371278506844883392, 371278514459434305, 371278548552695551, 371278548552867102, 371278547358978370, 371278541865565061, 371278542493173293, 371278542493365072, 371278549363760033, 371278558152683258]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 6130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 6100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362421958386919222, 362421958841386008⟩, ⟨347927793197431791, 347929686358207171⟩, true⟩

def words04 : List Nat := [371278564557860917, 371278564558032775, 371278546723252588, 371278551011981564, 371278563191380022, 371278563191554765, 371278553783975082, 371278544803601779, 371278535826082722, 371278532774127180]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 6140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 6100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362355377842239758, 362355378298259756⟩, ⟨758560494481851038, 758562397202695540⟩, true⟩

def words05 : List Nat := [371278540734681552, 371278557887247614, 371278570505914996, 371278570506087524, 371278557108807633, 371278551581512957, 371278561304074464, 371278561304246650, 371278541538391701, 371278521544558895]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 6150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 6100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362433567192747222, 362433567650307090⟩, ⟨277209421381026826, 277211333595519652⟩, true⟩

def words06 : List Nat := [371278501557134083, 371278501138734701, 371278507919153961, 371278524420565499, 371278536030935787, 371278536031108242, 371278512723402131, 371278500016376165, 371278496553466673, 371278496553645100]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 6160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 6100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362399213784663811, 362399214243794049⟩, ⟨489622489949149817, 489624411860823829⟩, true⟩

def words07 : List Nat := [371278489273123419, 371278474210674408, 371278470236882024, 371278471754951141, 371278477280800702, 371278482804928113, 371278485950308008, 371278485950480670, 371278454316711344, 371278441494904215]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 6170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 6100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362292829821124131, 362292830281795854⟩, ⟨1147809622835832412, 1147811554281961018⟩, true⟩

def words08 : List Nat := [371278428677154221, 371278426470380128, 371278401650852609, 371278375600643211, 371278349558790285, 371278331399007743, 371278300357892315, 371278287049527627, 371278273745402586, 371278260258254976]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 6180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 6100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362516776624075847, 362516777086313931⟩, ⟨(-239818214921683894), (-239816273771861460)⟩, true⟩

def words09 : List Nat := [371278230306833989, 371278218544023172, 371278207644264485, 371278207644438110, 371278182701723471, 371278149978816720, 371278117266402395, 371278110470196478, 371278097041960864, 371278103279867897]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 6190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 6100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 6100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk061
