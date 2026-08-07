import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk825

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592368016067625, 360592412454360730⟩, ⟨(-831809607598045529), (-829333655835576119)⟩, true⟩

def state01 : KState := ⟨⟨360596411399951752, 360596455849383271⟩, ⟨(-1165445733115808722), (-1162968862378056546)⟩, true⟩

def words00 : List Nat := [360582360151377765, 360582360294646528, 360582360351031603, 360582360407534344, 360582360408524779, 360582360455000255, 360582360662146129, 360582360869513694, 360582360964357848, 360582361136407086]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598794316932491, 360598838777527626⟩, ⟨(-1362148054559626866), (-1359670262656949434)⟩, true⟩

def words01 : List Nat := [360582361259660884, 360582361383261491, 360582361625864792, 360582361722151695, 360582361723242463, 360582361694460995, 360582361665435087, 360582361718394549, 360582361919024200, 360582362119917358]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594708333449344, 360594752805337551⟩, ⟨(-1025061764957380539), (-1022583041097555453)⟩, true⟩

def words02 : List Nat := [360582362235604584, 360582362362076511, 360582362484195878, 360582362606651164, 360582362690009707, 360582362691192609, 360582362628105225, 360582362491480142, 360582362363613724, 360582362515130265]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360559053804140169, 360559098287163777⟩, ⟨1917774909004192388, 1920254551925200552⟩, true⟩

def words03 : List Nat := [360582362812993435, 360582363111076535, 360582363275155992, 360582363363101535, 360582363364192420, 360582363365597251, 360582363366574946, 360582363306966556, 360582363100777134, 360582362820140821]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582809054030770, 360582853548221555⟩, ⟨(-43107906947958707), (-40627342233563955)⟩, true⟩

def words04 : List Nat := [360582362539243140, 360582362356002322, 360582362256402091, 360582362268146125, 360582362269237346, 360582362156009666, 360582361930854158, 360582361703092666, 360582361474976963, 360582361399825612]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360583219161075295, 360583263666545261⟩, ⟨(-77018771342084463), (-74537275473857205)⟩, true⟩

def words05 : List Nat := [360582361400898217, 360582361295823415, 360582361190521914, 360582361228708926, 360582361229708243, 360582361165562393, 360582361101298909, 360582360963529205, 360582360839668075, 360582360851953943]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 82550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 82500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585624619188490, 360585669135802631⟩, ⟨(-275664754164753906), (-273182338178613356)⟩, true⟩

def words06 : List Nat := [360582361010527669, 360582361022961939, 360582361024022483, 360582360932485226, 360582360840774673, 360582360643569941, 360582360618455009, 360582360679933294, 360582360680990707, 360582360682009186]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 82560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 82500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360601818104833289, 360601862632635510⟩, ⟨(-1612786783487913134), (-1610303443647036744)⟩, true⟩

def words07 : List Nat := [360582360869687311, 360582361057731226, 360582361350846139, 360582361653362745, 360582361828995479, 360582362004710140, 360582362202358972, 360582362473693498, 360582362710804005, 360582362948160304]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 82570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 82500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605615441657704, 360605659980731762⟩, ⟨(-1926482300156933324), (-1923998029431744812)⟩, true⟩

def words08 : List Nat := [360582363111748454, 360582363163709839, 360582363334395778, 360582363505439184, 360582363626019227, 360582363815048945, 360582363930351214, 360582364045787919, 360582364204717956, 360582364488130489]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 82580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 82500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584353542874192, 360584398093110603⟩, ⟨(-170283237216706489), (-167798044537933673)⟩, true⟩

def words09 : List Nat := [360582364917715982, 360582365347519162, 360582365654888698, 360582365859136547, 360582366026319138, 360582366193811741, 360582366476359306, 360582366612881904, 360582366638538099, 360582366664380468]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 82590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 82500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 82500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk825
