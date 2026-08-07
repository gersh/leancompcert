import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk240

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497746293434640, 362497754126524678⟩, ⟨(-306138470077691766), (-306011358622049424)⟩, true⟩

def state01 : KState := ⟨⟨362507201692417862, 362507209532241052⟩, ⟨(-533042747012416964), (-532915473925697896)⟩, true⟩

def words00 : List Nat := [371285006454366678, 371285007182926843, 371285007541738258, 371285007900753362, 371285008778644837, 371285008793460989, 371285010545426906, 371285012297559410, 371285013968183209, 371285014893370298]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 24000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 24000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362516679284490554, 362516687131134065⟩, ⟨(-760703829541453350), (-760576392664387492)⟩, true⟩

def words01 : List Nat := [371285016952749667, 371285019012346813, 371285021496950332, 371285021670712324, 371285021671297659, 371285021580048863, 371285021932428160, 371285021933260707, 371285022834178747, 371285024153212064]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 24010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 24000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492231507339561, 362492239360813774⟩, ⟨(-173522617381738880), (-173395016397572672)⟩, true⟩

def words02 : List Nat := [371285025218579557, 371285025219335604, 371285024465856407, 371285024957624339, 371285025905611802, 371285025906368231, 371285024897281802, 371285023882611311, 371285023587309140, 371285023888449013]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 24020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 24000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362452235560509397, 362452243420807399⟩, ⟨787832706234631628, 787960471229899524⟩, true⟩

def words03 : List Nat := [371285024887898790, 371285025887573198, 371285026881406271, 371285026882162705, 371285025861931602, 371285024650132061, 371285023438054237, 371285023192598108, 371285021841318259, 371285020478678860]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 24030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 24000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362516410808414721, 362516418675486111⟩, ⟨(-755237622234272564), (-755109694372184198)⟩, true⟩

def words04 : List Nat := [371285019115811729, 371285019023500286, 371285018849257772, 371285019628986209, 371285019903484903, 371285019904246762, 371285018911853547, 371285019181354800, 371285021182208452, 371285022488451386]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 24040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 24000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362504254478961932, 362504262352925964⟩, ⟨(-462685038850210708), (-462556945184427204)⟩, true⟩

def words05 : List Nat := [371285023789004619, 371285025089711171, 371285027810140383, 371285029882918563, 371285032140886563, 371285034398961325, 371285036326237610, 371285036409199904, 371285037208806720, 371285038008751390]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 24050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 24000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362506087038167729, 362506094918881483⟩, ⟨(-506714257889613289), (-506586001790652517)⟩, true⟩

def words06 : List Nat := [371285040538303828, 371285041071047782, 371285041585449815, 371285042100071925, 371285043130507878, 371285043550624474, 371285045222019393, 371285046893580565, 371285048553252880, 371285049428382931]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 24060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 24000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362539461107484307, 362539468995065895⟩, ⟨(-1310169141335788169), (-1310040719894163727)⟩, true⟩

def words07 : List Nat := [371285052031927131, 371285054635654919, 371285057707034416, 371285058478792564, 371285058971984096, 371285059465360461, 371285061686453539, 371285063049907839, 371285065309809311, 371285067569880307]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 24070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 24000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482251334122749, 362482259228539286⟩, ⟨67658679950516760, 67787266012985004⟩, true⟩

def words08 : List Nat := [371285069668470918, 371285069669228981, 371285070996408632, 371285072524240503, 371285074567629145, 371285074568387271, 371285074314162931, 371285073687757510, 371285073144896822, 371285073145766891]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 24080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 24000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482236389102791, 362482244290335940⟩, ⟨68244943213518977, 68373693523702141⟩, true⟩

def words09 : List Nat := [371285074638978320, 371285076249161821, 371285077849785530, 371285078033737628, 371285078608589645, 371285079183777848, 371285081484292558, 371285081489367250, 371285081489935651, 371285081373054766]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 24090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 24000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 24000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk240
