import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk263

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360630389911256342, 360630394024443283⟩, ⟨(-1250932295832130434), (-1250859121052434246)⟩, true⟩

def state01 : KState := ⟨⟨360618962673862901, 360618966790330494⟩, ⟨(-950792512308999134), (-950719251231266308)⟩, true⟩

def words00 : List Nat := [360582835350674973, 360582835351019858, 360582834623393812, 360582834635526617, 360582834635815463, 360582834275963352, 360582833963430154, 360582832664808173, 360582831508628864, 360582832882412465]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360556794517235270, 360556798636958803⟩, ⟨685314910493880456, 685388257251244608⟩, true⟩

def words01 : List Nat := [360582835320832692, 360582837759137719, 360582839079287131, 360582839571011568, 360582839571301089, 360582839371338728, 360582840411361137, 360582840411706203, 360582840213298747, 360582839224240386]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592399899276840, 360592404022255561⟩, ⟨(-251886379994027875), (-251812947543951111)⟩, true⟩

def words02 : List Nat := [360582838686044662, 360582840064849753, 360582841660931057, 360582843256955119, 360582843618375327, 360582843618720501, 360582842541874141, 360582841426767698, 360582840311645271, 360582840657873504]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603493264694876, 360603497390963419⟩, ⟨(-544147340220131821), (-544073821133290013)⟩, true⟩

def words03 : List Nat := [360582840658181273, 360582840114308730, 360582839570412122, 360582840780708686, 360582841248563298, 360582841716438174, 360582841716745998, 360582841457979394, 360582841588704631, 360582842373267307]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360573736329574536, 360573740459099064⟩, ⟨239450822115528123, 239524426981321683⟩, true⟩

def words04 : List Nat := [360582842696941316, 360582842697286759, 360582841584675538, 360582839756671920, 360582837928752658, 360582835159379092, 360582833115392601, 360582832509007538, 360582831902625096, 360582830570179950]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360606374950509687, 360606379083296002⟩, ⟨(-620955929737753704), (-620882238907713852)⟩, true⟩

def words05 : List Nat := [360582830290348262, 360582830355577704, 360582830821143001, 360582830821488558, 360582829852028445, 360582827495039109, 360582825138160498, 360582824234640391, 360582825128503296, 360582826022376170]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360553942534445248, 360553946670531609⟩, ⟨761327606482722918, 761401384318070440⟩, true⟩

def words06 : List Nat := [360582826022687404, 360582825983270163, 360582826847718810, 360582827712204422, 360582828205703149, 360582828206048903, 360582827265429482, 360582825003698776, 360582822742078509, 360582820443164073]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360506863645341082, 360506867784684832⟩, ⟨2003161781944937072, 2003235645694178518⟩, true⟩

def words07 : List Nat := [360582819687981327, 360582820027745713, 360582820028054144, 360582819440775605, 360582817420035176, 360582814965951696, 360582812511948219, 360582810468806207, 360582808329673375, 360582805451314635]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360541949350085744, 360541953492701326⟩, ⟨1077216882857357117, 1077290832933676533⟩, true⟩

def words08 : List Nat := [360582802573097012, 360582799531233851, 360582797212857988, 360582794857780584, 360582792502853940, 360582788938026170, 360582784430754005, 360582781356614650, 360582778282605756, 360582775426499495]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360552594567507931, 360552598713417579⟩, ⟨796226194862683399, 796300231885982503⟩, true⟩

def words09 : List Nat := [360582773879996029, 360582771475173492, 360582769070467231, 360582768098166255, 360582767963741313, 360582767459431765, 360582766955130968, 360582765317149235, 360582762743168431, 360582761600989018]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk263
