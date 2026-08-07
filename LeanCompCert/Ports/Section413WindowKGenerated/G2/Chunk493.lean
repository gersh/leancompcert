import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk493

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

def state06 : KState := ⟨⟨360545538221071168, 360545553489532674⟩, ⟨1792540841788446750, 1793050096436732452⟩, true⟩

def words05 : List Nat := [360581881951354983, 360581882278655442, 360581882401162886, 360581882401843162, 360581882114417178, 360581881725547106, 360581881336499062, 360581880729949028, 360581880199183943, 360581879463933743]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592543026265529, 360592558301148303⟩, ⟨(-527877094889075491), (-527367523255161073)⟩, true⟩

def words06 : List Nat := [360581878728561807, 360581878115541685, 360581877800174420, 360581877847436231, 360581877848069327, 360581877550724812, 360581876843482528, 360581876545470421, 360581876357497786, 360581876574562754]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586758900011505, 360586774181381007⟩, ⟨(-242284529380558923), (-241774637464494161)⟩, true⟩

def words07 : List Nat := [360581876575179309, 360581876474041342, 360581876566934015, 360581877029435974, 360581877350227063, 360581877671115501, 360581877766278298, 360581877875195452, 360581877974905078, 360581878074832649]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360542813200504784, 360542828488281951⟩, ⟨1927861811116637146, 1928372019474799446⟩, true⟩

def words08 : List Nat := [360581878152539085, 360581878153219725, 360581877821493356, 360581877227472791, 360581876633376720, 360581875676023492, 360581874925652977, 360581874123272882, 360581873320850973, 360581872262719587]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360567510632730633, 360567525926940670⟩, ⟨707976170691806700, 708486696800993770⟩, true⟩

def words09 : List Nat := [360581871472766210, 360581871091732898, 360581870737374405, 360581870738055286, 360581870356236326, 360581869589260531, 360581868822185404, 360581868333947952, 360581868052524250, 360581867762908302]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk493
