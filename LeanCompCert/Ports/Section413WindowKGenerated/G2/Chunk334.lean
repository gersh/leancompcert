import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk334

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360513564649843699, 360513571420431815⟩, ⟨2259895477250419000, 2260048377930445886⟩, true⟩

def state01 : KState := ⟨⟨360575703834173526, 360575710608973340⟩, ⟨184155361460776877, 184308402832610649⟩, true⟩

def words00 : List Nat := [360581235514021368, 360581234155712359, 360581233411209057, 360581233486487706, 360581233486900161, 360581232679182335, 360581230977874667, 360581229411490516, 360581227845064701, 360581227172961147]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591648125219835, 360591654904273976⟩, ⟨(-348728878128674621), (-348575694598796451)⟩, true⟩

def words01 : List Nat := [360581227008253819, 360581226034202259, 360581225060123695, 360581225350415831, 360581225350789699, 360581225258711416, 360581225166593797, 360581224532026870, 360581224751323546, 360581225063916154]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584758158716484, 360584764941974912⟩, ⟨(-118468785480059306), (-118315461421467500)⟩, true⟩

def words02 : List Nat := [360581225767766783, 360581226188121604, 360581226188521332, 360581226037901487, 360581225887224748, 360581225095855485, 360581225313802231, 360581225869626023, 360581225870026595, 360581225847678557]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599186090566454, 360599192878047928⟩, ⟨(-600787303900845446), (-600633838644885760)⟩, true⟩

def words03 : List Nat := [360581226578770509, 360581227309957794, 360581228660177897, 360581229414832872, 360581229415248517, 360581229411936905, 360581229880200479, 360581230801832603, 360581231339344600, 360581231876922218]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590143305312234, 360590150097045148⟩, ⟨(-298520482707318278), (-298366875261802966)⟩, true⟩

def words04 : List Nat := [360581231877320404, 360581231859268966, 360581231633917144, 360581231822487157, 360581231822861225, 360581231784381928, 360581231770698361, 360581231308976481, 360581230847198580, 360581230576694133]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360525681889568073, 360525688685514939⟩, ⟨1858091559443893996, 1858245307867062994⟩, true⟩

def words05 : List Nat := [360581230978229094, 360581231379823094, 360581231380232437, 360581231044881470, 360581230171683373, 360581229072098479, 360581227972447136, 360581227764394416, 360581226666091850, 360581225006730333]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595043617331087, 360595050417496968⟩, ⟨(-463000595444862490), (-462846705832710598)⟩, true⟩

def words06 : List Nat := [360581223347359148, 360581222579553700, 360581223205371514, 360581223862326226, 360581223862739120, 360581223632768426, 360581222953181420, 360581222243177878, 360581221713543521, 360581222127161074]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577007348428635, 360577014152858249⟩, ⟨140653817460441261, 140807849800682033⟩, true⟩

def words07 : List Nat := [360581222127563273, 360581222091876767, 360581222056110350, 360581222063050403, 360581222063427038, 360581221866060595, 360581221668657229, 360581221023964221, 360581220008246681, 360581219883139035]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360562213667555680, 360562220476204021⟩, ⟨635803133143501177, 635957306748143853⟩, true⟩

def words08 : List Nat := [360581219757891720, 360581219606339080, 360581218565924399, 360581217078587578, 360581215591263986, 360581213673181477, 360581212202976807, 360581211622936017, 360581211042874436, 360581209944903578]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588297465378691, 360588304278249510⟩, ⟨(-237883553034211325), (-237729237998143719)⟩, true⟩

def words09 : List Nat := [360581209488595091, 360581209599412989, 360581210599755409, 360581210711828030, 360581210712250954, 360581209885852729, 360581209059419261, 360581208138635838, 360581207882621411, 360581208094911755]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk334
