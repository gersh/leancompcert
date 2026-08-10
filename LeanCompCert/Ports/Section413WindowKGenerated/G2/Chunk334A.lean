import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk334A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk334A
