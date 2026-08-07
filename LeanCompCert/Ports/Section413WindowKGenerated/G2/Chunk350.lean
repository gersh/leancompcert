import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk350

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

def state06 : KState := ⟨⟨360630811391237150, 360630818881574304⟩, ⟨(-1715401967128694739), (-1715224424299734887)⟩, true⟩

def words05 : List Nat := [360581892008789150, 360581892240493735, 360581893284687034, 360581894065904068, 360581894123490076, 360581894181112678, 360581894356750101, 360581894940369893, 360581896336184787, 360581897732026381]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 35050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 35000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360605308799704740, 360605316294525279⟩, ⟨(-821492875496924464), (-821315175458234596)⟩, true⟩

def words06 : List Nat := [360581898540583115, 360581898832844451, 360581899102001396, 360581899371278840, 360581899436863533, 360581899437333902, 360581898928631612, 360581898010198698, 360581897091725072, 360581897653042053]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 35060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 35000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360538937121197229, 360538944620445871⟩, ⟨1506680738646537834, 1506858594000999800⟩, true⟩

def words07 : List Nat := [360581898586779016, 360581899520551808, 360581900034402374, 360581900738854530, 360581900958967234, 360581901179191127, 360581901376671431, 360581901377141907, 360581900764489936, 360581899540457303]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 35070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 35000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360626817422906834, 360626824926595912⟩, ⟨(-1576607581541397117), (-1576429570394577227)⟩, true⟩

def words08 : List Nat := [360581898316388065, 360581897905577656, 360581898718958379, 360581899532391062, 360581899651301302, 360581899651772010, 360581899259418939, 360581899104004404, 360581899603494990, 360581900884237628]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 35080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 35000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360647982334374414, 360647989842553628⟩, ⟨(-2319558326483657552), (-2319380157756559846)⟩, true⟩

def words09 : List Nat := [360581901519386111, 360581902154539064, 360581903137857487, 360581904527932785, 360581905714834429, 360581906901745528, 360581907679428758, 360581908752202244, 360581910635234996, 360581912518324787]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 35090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 35000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 35000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk350
