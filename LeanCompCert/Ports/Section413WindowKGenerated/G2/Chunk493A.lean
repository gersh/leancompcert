import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk493A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360556839815375125, 360556855045231454⟩, ⟨1233706542728921188, 1234213892985361474⟩, true⟩

def state01 : KState := ⟨⟨360586033888779169, 360586049125057553⟩, ⟨(-205711424284927350), (-205203757389679002)⟩, true⟩

def words00 : List Nat := [360581889302559494, 360581888787164139, 360581888664076536, 360581888742419257, 360581888743046933, 360581888484063275, 360581887930156804, 360581887786484819, 360581887642609145, 360581887705548931]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 49300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 49300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360555412122949875, 360555427365697936⟩, ⟨1304404768372493605, 1304912754320361801⟩, true⟩

def words01 : List Nat := [360581887706159804, 360581887583691874, 360581887461101359, 360581887549398850, 360581887549977355, 360581887407679187, 360581887265314124, 360581886831182736, 360581885986427195, 360581885450740928]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 49310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 49300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360560410454385158, 360560425703544567⟩, ⟨1057863012995285155, 1058371315182097329⟩, true⟩

def words02 : List Nat := [360581884914844710, 360581884380100860, 360581884024387529, 360581883410311235, 360581882796143420, 360581882071502569, 360581881554323402, 360581881360359663, 360581881166346788, 360581880625806520]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 49320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 49300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360619232259672129, 360619247515247980⟩, ⟨(-1844138243902647817), (-1843629625160572879)⟩, true⟩

def words03 : List Nat := [360581880191438484, 360581880166892853, 360581880526445223, 360581880780414547, 360581880781049459, 360581880612249455, 360581880586720306, 360581880935320926, 360581881693199077, 360581882451200625]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 49330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 49300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591055620372061, 360591070882433073⟩, ⟨(-454008023260251146), (-453499084509024206)⟩, true⟩

def words04 : List Nat := [360581883004242480, 360581883147247831, 360581883147808674, 360581883112235620, 360581883076484042, 360581882863180299, 360581882591223115, 360581882112323150, 360581881633309130, 360581881624170647]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 49340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 49300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk493A
