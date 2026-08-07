import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk361

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360529438137241241, 360529446097623857⟩, ⟨1896430079790261520, 1896624348094799380⟩, true⟩

def state01 : KState := ⟨⟨360627448585894022, 360627456550857605⟩, ⟨(-1642345588774633544), (-1642151155074807732)⟩, true⟩

def words00 : List Nat := [360581982713294587, 360581981485520280, 360581980856557971, 360581980785040925, 360581980713490379, 360581979976190164, 360581979320105903, 360581979375292157, 360581980196018518, 360581981455870626]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 36100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 36100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571825643771980, 360571833613363951⟩, ⟨366466269757772362, 366660870611404596⟩, true⟩

def words01 : List Nat := [360581982329398479, 360581983202931331, 360581983596035943, 360581984467961764, 360581985004005758, 360581985540099003, 360581985692368017, 360581985692853562, 360581985080743342, 360581984800257955]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 36110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 36100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360526962891563741, 360526970865726076⟩, ⟨1987114733166888840, 1987309499125225120⟩, true⟩

def words02 : List Nat := [360581984680295904, 360581984680781495, 360581984077639679, 360581983088727653, 360581982099789523, 360581980667950544, 360581979665744059, 360581978332416277, 360581976999109298, 360581975280315759]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 36120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 36100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360615376761441710, 360615384740187236⟩, ⟨(-1207757266294699166), (-1207562334723314784)⟩, true⟩

def words03 : List Nat := [360581973758347848, 360581973001299588, 360581972244151720, 360581971839344407, 360581971734602980, 360581970891710287, 360581970048771346, 360581970357742401, 360581971282716973, 360581972207752514]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 36130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 36100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360628486720685346, 360628494704062355⟩, ⟨(-1681851274765814500), (-1681656175789813978)⟩, true⟩

def words04 : List Nat := [360581972546858991, 360581972637367375, 360581973237543818, 360581973837834089, 360581974244232134, 360581974829402333, 360581975029236840, 360581975229121754, 360581975860470875, 360581977147817997]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 36140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 36100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360545677627685539, 360545685615636500⟩, ⟨1312305261705858746, 1312500526053503490⟩, true⟩

def words05 : List Nat := [360581979198660550, 360581981249482654, 360581982789255775, 360581983565960185, 360581983818573101, 360581984071294395, 360581984117159610, 360581984117645728, 360581983646772968, 360581982643458777]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 36150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 36100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599943760007782, 360599951752553748⟩, ⟨(-650095825017498569), (-649900394492187683)⟩, true⟩

def words06 : List Nat := [360581981640090187, 360581981819183399, 360581982440560232, 360581983061995228, 360581983062443361, 360581983037740084, 360581983187402458, 360581983510578774, 360581983811920888, 360581984309173909]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 36160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 36100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552465636649196, 360552473633829908⟩, ⟨1067596923937474030, 1067792522124114678⟩, true⟩

def words07 : List Nat := [360581984424629025, 360581984540126860, 360581985167161494, 360581986178784608, 360581986984090869, 360581987789442184, 360581988168317644, 360581988168803968, 360581987785737597, 360581986970538701]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 36170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 36100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583686269031824, 360583694270795339⟩, ⟨(-62290892860253544), (-62095128844998534)⟩, true⟩

def words08 : List Nat := [360581986155218354, 360581985872198023, 360581985076350865, 360581983697184769, 360581982318015587, 360581980745467356, 360581979697904842, 360581979412772298, 360581979127606348, 360581978509173804]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 36180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 36100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360601759602997858, 360601767609349573⟩, ⟨(-716470674296765293), (-716274744211345569)⟩, true⟩

def words09 : List Nat := [360581979319127020, 360581980129180845, 360581981191600979, 360581981492834776, 360581981493284209, 360581981150413994, 360581980807476432, 360581980466701684, 360581981013701450, 360581981560781541]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 36190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 36100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 36100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk361
