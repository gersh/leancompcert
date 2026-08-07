import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk076

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360440395753700479, 360440396059180576⟩, ⟨1074869130851656427, 1074870705134997917⟩, true⟩

def state01 : KState := ⟨⟨360607171886220043, 360607172192544689⟩, ⟨(-193117618429308104), (-193116037723124986)⟩, true⟩

def words00 : List Nat := [360581807808383210, 360581791505790488, 360581802516014321, 360581816614624513, 360581816614707979, 360581815919377825, 360581798114710665, 360581797494712394, 360581796874852490, 360581798912066024]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 7600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 7600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360563535292980543, 360563535600157729⟩, ⟨139026855166410709, 139028442364647397⟩, true⟩

def words01 : List Nat := [360581798912145790, 360581790686759224, 360581782463516138, 360581789549713345, 360581793432018084, 360581797313319655, 360581797313399458, 360581792452924177, 360581783197163753, 360581780802567788]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 7610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 7600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360639702561755071, 360639702869776963⟩, ⟨(-442037056601316547), (-442035462962245075)⟩, true⟩

def words02 : List Nat := [360581793120108421, 360581800501033661, 360581800501116061, 360581791855129072, 360581783211395484, 360581768257775359, 360581768924839699, 360581773308906186, 360581773308986070, 360581776587119088]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 7620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 7600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360802933675505379, 360802933984374306⟩, ⟨(-1688882504893153022), (-1688880904786924064)⟩, true⟩

def words03 : List Nat := [360581788509082690, 360581800427949003, 360581817515405160, 360581833062889072, 360581834051840325, 360581835040539871, 360581835406605587, 360581847336115009, 360581876274230759, 360581905204792194]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 7630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 7600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360708136090213971, 360708136399939396⟩, ⟨(-965432794444838451), (-965431187790862691)⟩, true⟩

def words04 : List Nat := [360581925559007332, 360581928963732675, 360581949365985155, 360581969762928292, 360581978402320725, 360581978402410652, 360581970104150630, 360581953154464439, 360581936244569151, 360581952739268783]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 7640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 7600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360415234408768146, 360415234719342216⟩, ⟨1276955039807671515, 1276956652958057769⟩, true⟩

def words05 : List Nat := [360581968629015061, 360581984514624678, 360581991768985406, 360581991769075451, 360581990936891774, 360581985618285349, 360581980301042002, 360581970098637171, 360581961008968106, 360581939243227080]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 7650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 7600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360527237645115408, 360527237956540461⟩, ⟨418405055004869500, 418406674677973662⟩, true⟩

def words06 : List Nat := [360581917483148191, 360581905345794281, 360581908126531861, 360581914305938493, 360581914306022921, 360581904580389943, 360581878024234792, 360581842721778486, 360581807428501731, 360581789022339415]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 7660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 7600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360535908886429835, 360535909198715346⟩, ⟨352104512117062866, 352106138394345490⟩, true⟩

def words07 : List Nat := [360581781911082917, 360581766247488089, 360581751793842932, 360581761691410164, 360581766632973266, 360581771573263763, 360581771573344959, 360581767750324376, 360581762322508246, 360581756352152110]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 7670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 7600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360636126025425379, 360636126338562917⟩, ⟨(-417989588569234942), (-417987955744120954)⟩, true⟩

def words08 : List Nat := [360581761242834274, 360581765856916273, 360581765856997175, 360581759952490836, 360581754049506350, 360581739081593729, 360581753474555028, 360581769072961106, 360581771597800352, 360581778665211712]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 7680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 7600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360781841608384932, 360781841922378513⟩, ⟨(-1539770500920104600), (-1539768861507806856)⟩, true⟩

def words09 : List Nat := [360581802532235432, 360581826393080446, 360581848328746388, 360581853562784743, 360581853562869138, 360581844845991930, 360581836757402224, 360581845966694415, 360581871940268576, 360581897907119741]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 7690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 7600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 7600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk076
