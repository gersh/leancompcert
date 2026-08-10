import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk402A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk402B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk402A

def state06 : KState := ⟨⟨360602682991718933, 360602692980920248⟩, ⟨(-805384430364043474), (-805112619355412750)⟩, true⟩

def words05 : List Nat := [360582688685562809, 360582689179253318, 360582690288731606, 360582691707034968, 360582692849059836, 360582693991118578, 360582694629472156, 360582694653531918, 360582695150702550, 360582695648033450]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360586980964126165, 360586990958460580⟩, ⟨(-173249644838690028), (-172977627144944308)⟩, true⟩

def words06 : List Nat := [360582696031842099, 360582696063500381, 360582696063986496, 360582695787096555, 360582695510122086, 360582695076370701, 360582695257647634, 360582695559514511, 360582695560001076, 360582695618708775]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360601621988690474, 360601631988185332⟩, ⟨(-763160532104129827), (-762888306574311055)⟩, true⟩

def words07 : List Nat := [360582695619160786, 360582695399095507, 360582695178883240, 360582694840462457, 360582694325873152, 360582693287261617, 360582692248597270, 360582691886713813, 360582692357366458, 360582692828120431]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598970025221354, 360598980029913094⟩, ⟨(-656511043179815730), (-656238608293941944)⟩, true⟩

def words08 : List Nat := [360582692923562818, 360582692929099210, 360582693549597871, 360582694170231666, 360582694366788974, 360582694367334971, 360582693950614100, 360582693145998325, 360582692341318089, 360582692556077897]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360533216343394904, 360533226353237426⟩, ⟨1993151991790467795, 1993424634226333099⟩, true⟩

def words09 : List Nat := [360582693345177754, 360582694134352176, 360582694393891580, 360582694394437705, 360582694040852504, 360582693530643023, 360582693020298174, 360582692922294163, 360582692211231239, 360582690984359668]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk402B
