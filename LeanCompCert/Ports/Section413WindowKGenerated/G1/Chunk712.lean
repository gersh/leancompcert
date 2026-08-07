import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk712

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362463741283110240, 362463816617197715⟩, ⟨1522714508451446111, 1526336942667712805⟩, true⟩

def state01 : KState := ⟨⟨362468452614589484, 362468527970511194⟩, ⟨1187256967254572186, 1190880956179880154⟩, true⟩

def words00 : List Nat := [371285253634389800, 371285253466116516, 371285253198165559, 371285253033270521, 371285252867597707, 371285252661658924, 371285252192239391, 371285251889049888, 371285251584549486, 371285251477830109]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 71200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 71200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362472224467739221, 362472299845905255⟩, ⟨918626854185535170, 922252427242758200⟩, true⟩

def words01 : List Nat := [371285251244842200, 371285250972094173, 371285250698382503, 371285250507691182, 371285250270314918, 371285250093719152, 371285249916290308, 371285249726066604, 371285249370805373, 371285249191977184]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 71210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 71200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362459950531446888, 362460025931336767⟩, ⟨1792853764703708243, 1796480885046866497⟩, true⟩

def words02 : List Nat := [371285249011814224, 371285249000923134, 371285248744280250, 371285248488850703, 371285248232514089, 371285247941794634, 371285247552610465, 371285247294465448, 371285247035525675, 371285246777680259]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 71220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 71200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362473014424077108, 362473089846103072⟩, ⟨862246401474449169, 865875098677775243⟩, true⟩

def words03 : List Nat := [371285246425271349, 371285246160236293, 371285245893854930, 371285245825035039, 371285245493192844, 371285245131565931, 371285244768960223, 371285244604149466, 371285244352773856, 371285244184939088]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 71230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 71200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468817437411132, 362468892881461455⟩, ⟨1161210221576624083, 1164840487907477231⟩, true⟩

def words04 : List Nat := [371285244016155873, 371285243848405946, 371285243438223083, 371285243210854704, 371285242982285079, 371285242814291347, 371285242484657489, 371285242097806382, 371285241709939757, 371285241519888227]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 71240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 71200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362470749386863328, 362470824852903360⟩, ⟨1023575597415047551, 1027207430626307591⟩, true⟩

def words05 : List Nat := [371285241292094182, 371285241229575274, 371285241166316789, 371285241063158465, 371285240747012000, 371285240491913462, 371285240235534714, 371285240176587491, 371285239975672034, 371285239776150993]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478146663572698, 362478222151465846⟩, ⟨496500872839761013, 500134263416504849⟩, true⟩

def words06 : List Nat := [371285239575524380, 371285239572561733, 371285239582202431, 371285239687181086, 371285239759656060, 371285239762110242, 371285239646187206, 371285239613913859, 371285239607382911, 371285239609911427]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481207423926925, 362481282934129478⟩, ⟨278380844517448386, 282015825191298398⟩, true⟩

def words07 : List Nat := [371285239513293192, 371285239417012245, 371285239400064812, 371285239412625180, 371285239485933886, 371285239560152218, 371285239618802752, 371285239621245818, 371285239437493847, 371285239385100176]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469629356980163, 362469704888940545⟩, ⟨1103709015472660856, 1107345547157492666⟩, true⟩

def words08 : List Nat := [371285239331286071, 371285239307740351, 371285239069712062, 371285238832905703, 371285238595192577, 371285238404422051, 371285238121740997, 371285238036609475, 371285237950598205, 371285237860565703]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483139204170525, 362483214758198796⟩, ⟨140529898423418746, 144168003437110728⟩, true⟩

def words09 : List Nat := [371285237644353197, 371285237531344151, 371285237497614252, 371285237500058702, 371285237352481223, 371285237140173157, 371285236926841736, 371285236892705052, 371285236775459752, 371285236749831856]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk712
