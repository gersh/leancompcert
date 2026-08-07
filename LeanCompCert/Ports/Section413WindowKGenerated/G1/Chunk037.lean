import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk037

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362402608679120805, 362402608835662057⟩, ⟨257084026223704379, 257084419130065231⟩, true⟩

def state01 : KState := ⟨⟨362633879658490053, 362633879815915884⟩, ⟨(-599500253149461218), (-599499856965578828)⟩, true⟩

def words00 : List Nat := [371272126271340249, 371272144163183748, 371272181442107437, 371272218700946707, 371272253232350906, 371272253232449894, 371272218309204005, 371272217921773329, 371272289557869780, 371272333101562454]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 3700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 3700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362823520305446165, 362823520463774774⟩, ⟨(-1304171803620893192), (-1304171404083106176)⟩, true⟩

def words01 : List Nat := [371272376398651191, 371272419672452356, 371272519057035903, 371272582454516140, 371272667577292046, 371272752654302583, 371272820166425403, 371272842484535180, 371272936752876789, 371273030970605437]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 3710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 3700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362679924261789496, 362679924421002566⟩, ⟨(-768876991724637758), (-768876588892058982)⟩, true⟩

def words02 : List Nat := [371273187353587188, 371273248069534103, 371273301504766884, 371273354911343519, 371273426072973885, 371273466654818364, 371273578908483017, 371273691101982854, 371273791287148723, 371273846536014076]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 3720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 3700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362934822352680035, 362934822512792562⟩, ⟨(-1721775391252686200), (-1721774985060485984)⟩, true⟩

def words03 : List Nat := [371273909165848453, 371273971762176216, 371274105904805535, 371274144898769269, 371274173961927691, 371274203009562523, 371274279899668548, 371274331743674522, 371274454869616628, 371274577929777196]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 3730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 3700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362505367427903996, 362505367588917514⟩, ⟨(-114234557126547154), (-114234147560059298)⟩, true⟩

def words04 : List Nat := [371274694159885324, 371274715638065076, 371274788620718691, 371274861564449910, 371274936913789395, 371274936913889299, 371274917740858531, 371274898297813084, 371274905149454422, 371274913270719685]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 3740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 3700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362057796763677276, 362057796925593777⟩, ⟨1567553988948002907, 1567554401905336979⟩, true⟩

def words05 : List Nat := [371274952585669140, 371274991879709607, 371275031567030214, 371275031567130214, 371274977196183020, 371274943909730550, 371274910640948424, 371274907527684729, 371274810599836631, 371274699692057963]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 3750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 3700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362632023797081813, 362632023959896343⟩, ⟨(-594084167987223922), (-594083751648669992)⟩, true⟩

def words06 : List Nat := [371274588843212085, 371274548416073200, 371274488655034727, 371274482576289267, 371274476500743080, 371274458615744946, 371274384270516350, 371274380149840659, 371274442062802974, 371274483850734670]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 3760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 3700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362535120455673182, 362535120619406034⟩, ⟨(-228330031358251058), (-228329611553025584)⟩, true⟩

def words07 : List Nat := [371274524551087516, 371274565229897910, 371274614249449137, 371274635484925607, 371274675056130435, 371274714606420864, 371274753746142147, 371274753746242868, 371274715960138829, 371274731936107165]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 3770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 3700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362318564709019979, 362318564873651211⟩, ⟨592000832338916466, 592001255544789356⟩, true⟩

def words08 : List Nat := [371274799137168536, 371274799137269408, 371274794203167461, 371274783327424506, 371274782255640627, 371274782255751620, 371274760637604316, 371274763549776042, 371274765732529588, 371274765732634006]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 3780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 3700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362737317187837032, 362737317353385005⟩, ⟨(-997129033465292539), (-997128606780386375)⟩, true⟩

def words09 : List Nat := [371274724529627741, 371274722266686118, 371274786949083222, 371274798073202171, 371274798073281348, 371274783902398377, 371274824679756858, 371274846016854598, 371274915088328145, 371274984123503294]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 3790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 3700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 3700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk037
