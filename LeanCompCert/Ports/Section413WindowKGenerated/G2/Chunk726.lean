import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk726

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583202968074931, 360583237037313136⟩, ⟨(-63319868571152727), (-61649206749803143)⟩, true⟩

def state01 : KState := ⟨⟨360581953351701937, 360581987430638802⟩, ⟨27390898039754096, 29062264033682284⟩, true⟩

def words00 : List Nat := [360582388040380729, 360582388082623145, 360582388083551229, 360582388030316058, 360582387976900454, 360582387821337802, 360582387765213562, 360582387770395844, 360582387771314550, 360582387682174868]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360593344833711580, 360593378922399397⟩, ⟨(-799937799796741690), (-798265725740161892)⟩, true⟩

def words01 : List Nat := [360582387677518150, 360582387512048670, 360582387368953870, 360582387369985059, 360582387204306042, 360582386870474349, 360582386536453503, 360582386401656600, 360582386553860918, 360582386706294687]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360587470420375542, 360587504518887069⟩, ⟨(-373381241152403827), (-371708453650296349)⟩, true⟩

def words02 : List Nat := [360582386762707092, 360582386792187082, 360582387010702404, 360582387229517519, 360582387315236062, 360582387316267408, 360582387212772055, 360582386993493816, 360582386774024172, 360582386753006794]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360545679783973202, 360545713892211662⟩, ⟨2662118454208564991, 2663791948227009709⟩, true⟩

def words03 : List Nat := [360582386805957402, 360582386859117604, 360582386860043806, 360582386762333136, 360582386577268105, 360582386323617994, 360582386069674028, 360582385899796427, 360582385540646497, 360582385036873378]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590488887685229, 360590523005662485⟩, ⟨(-593073576664955325), (-591399375171306819)⟩, true⟩

def words04 : List Nat := [360582384532882704, 360582384094496308, 360582383751291479, 360582383597441469, 360582383443504635, 360582383122300647, 360582382806235583, 360582382679609760, 360582382614019640, 360582382727136776]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360573113360117664, 360573147487938383⟩, ⟨669300110473225353, 670975027141582979⟩, true⟩

def words05 : List Nat := [360582382728056425, 360582382727202382, 360582382726165116, 360582382717514402, 360582382718383987, 360582382639726311, 360582382560971551, 360582382343323046, 360582382062321873, 360582381936426432]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578311049752467, 360578345187287589⟩, ⟨291595238330362013, 293270860895703719⟩, true⟩

def words06 : List Nat := [360582381872147264, 360582381873179576, 360582381809780678, 360582381638387719, 360582381466830525, 360582381247512274, 360582381175155063, 360582381094762353, 360582381014258985, 360582380839701181]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360620693920625707, 360620728067899346⟩, ⟨(-2788573384687511399), (-2786897054376272413)⟩, true⟩

def words07 : List Nat := [360582380918481477, 360582381053094076, 360582381376405637, 360582381765965611, 360582381980881473, 360582382195856835, 360582382440050677, 360582382779813356, 360582383308238555, 360582383836884690]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601614270456331, 360601648427571594⟩, ⟨(-1401931342157610934), (-1400254296507299712)⟩, true⟩

def words08 : List Nat := [360582384217758953, 360582384409792091, 360582384657806476, 360582384906124597, 360582385106141051, 360582385117403585, 360582385118323459, 360582385035447585, 360582385057340543, 360582385323521474]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578048604438562, 360578082771274004⟩, ⟨311245423660089000, 312923175918544570⟩, true⟩

def words09 : List Nat := [360582385742246824, 360582386161161063, 360582386464669572, 360582386686267582, 360582386756410232, 360582386826814078, 360582387049379604, 360582387136269248, 360582387137195542, 360582387079058304]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk726
