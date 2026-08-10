import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk350A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581871448873932, 360581878912542731⟩, ⟨1477627758262614, 1654236396138234⟩, true⟩

def state01 : KState := ⟨⟨360563315504981142, 360563322973122441⟩, ⟨650893238579036558, 651070003776693012⟩, true⟩

def words00 : List Nat := [360581926175511381, 360581925766683984, 360581925635089724, 360581925368826492, 360581925102454346, 360581924631823539, 360581923795912594, 360581922338243193, 360581920880569028, 360581919659891270]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 35000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 35000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360525539912544569, 360525547385105200⟩, ⟨1973785340615641708, 1973962260556585242⟩, true⟩

def words01 : List Nat := [360581919189067528, 360581919249497155, 360581919249918245, 360581918695868220, 360581918473159067, 360581917879365691, 360581917285469654, 360581916902529101, 360581915706401930, 360581914097285571]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 35010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 35000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581328268894814, 360581335745895596⟩, ⟨19756596779182506, 19933672235723076⟩, true⟩

def words02 : List Nat := [360581912488160200, 360581910856234130, 360581909743497226, 360581909445039006, 360581909146558377, 360581908172494575, 360581906623338567, 360581905888404936, 360581905153362647, 360581904791634555]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 35020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 35000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360539113141178127, 360539120622649704⟩, ⟨1498822199997996276, 1498999432088686948⟩, true⟩

def words03 : List Nat := [360581904775808943, 360581904348987892, 360581904052556113, 360581904592273384, 360581904592677979, 360581904323011776, 360581904053313587, 360581903186422862, 360581901507187640, 360581900286807487]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 35030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 35000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360561502003797583, 360561509489700847⟩, ⟨714242172072621857, 714419559471469579⟩, true⟩

def words04 : List Nat := [360581899066341551, 360581898406603252, 360581897772559486, 360581896728176711, 360581895683777011, 360581894255863216, 360581893509658155, 360581893332613838, 360581893155533290, 360581892358729991]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 35040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 35000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk350A
