import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk179

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497186525671671, 362497190773794166⟩, ⟨(-208227713184909685), (-208176279401808043)⟩, true⟩

def state01 : KState := ⟨⟨362483829091404652, 362483833344498800⟩, ⟨30711657040963790, 30763179841968776⟩, true⟩

def words00 : List Nat := [371285561910194007, 371285561910744660, 371285558207556562, 371285557617936891, 371285557377775426, 371285557378335565, 371285555147654691, 371285552727235096, 371285550997681767, 371285550998314656]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 17900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 17900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362457234511014433, 362457238769080774⟩, ⟨507452687491579188, 507504299369749822⟩, true⟩

def words01 : List Nat := [371285553917847707, 371285556933171151, 371285559310494975, 371285559311048564, 371285559618881405, 371285560242885345, 371285561930107305, 371285561930660152, 371285560901340513, 371285559321500961]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 17910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 17900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362512864609320935, 362512868872315478⟩, ⟨(-489523603171437893), (-489471902954689859)⟩, true⟩

def words02 : List Nat := [371285559269522976, 371285559598396159, 371285563034558458, 371285566470555497, 371285569352726942, 371285569353278136, 371285568095333996, 371285567636963142, 371285569825285336, 371285571348309305]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 17920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 17900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362523181310016334, 362523185578026274⟩, ⟨(-674485276493107586), (-674433486325137020)⟩, true⟩

def words03 : List Nat := [371285572792567628, 371285574236845203, 371285578266742612, 371285581209722117, 371285584364646520, 371285587519436643, 371285590647954646, 371285590648506213, 371285591737529372, 371285593833623781]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 17930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 17900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362446096710834841, 362446100983761058⟩, ⟨708692403727271997, 708744282119246801⟩, true⟩

def words04 : List Nat := [371285596183584309, 371285596184136152, 371285594400538486, 371285592614976599, 371285590829398907, 371285589341935646, 371285586330969791, 371285585969724139, 371285585608328279, 371285585344881908]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 17940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 17900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362539854864472592, 362539859142393205⟩, ⟨(-974825677585523082), (-974773709519558802)⟩, true⟩

def words05 : List Nat := [371285583234942455, 371285583324854172, 371285585428977547, 371285585429529850, 371285584079162558, 371285582183022220, 371285581486772150, 371285581487380279, 371285584436338950, 371285587458772051]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 17950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 17900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362465559246334765, 362465563529243952⟩, ⟨359876642104975126, 359928699791692574⟩, true⟩

def words06 : List Nat := [371285590479379591, 371285590940607349, 371285592167254897, 371285593394047209, 371285595555021472, 371285595555576588, 371285594791764924, 371285594039733004, 371285593287561668, 371285592950490012]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 17960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 17900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493410489208057, 362493414777088892⟩, ⟨(-140476631724613833), (-140424484672031259)⟩, true⟩

def words07 : List Nat := [371285593814375890, 371285595792801650, 371285597743647809, 371285597809763088, 371285598798881690, 371285599788177395, 371285603867616345, 371285604303579531, 371285604738392945, 371285605173358731]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 17970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 17900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362570477951694950, 362570482244532472⟩, ⟨(-1526517638037158138), (-1526465401838068378)⟩, true⟩

def words08 : List Nat := [371285608698022477, 371285610761872495, 371285614039103000, 371285617316194162, 371285619743832915, 371285619744388434, 371285622520042500, 371285625452056224, 371285631471196444, 371285636188068792]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 17980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 17900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362546601978401591, 362546606276289352⟩, ⟨(-1096742275237745879), (-1096689948159938603)⟩, true⟩

def words09 : List Nat := [371285640880344755, 371285645572289188, 371285652489422112, 371285657865997442, 371285663650752913, 371285669435075443, 371285674607729993, 371285675670838449, 371285679056248450, 371285682441604616]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 17990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 17900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 17900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk179
