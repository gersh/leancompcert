import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk931

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488301922867332, 362488433423399354⟩, ⟨(-315595230456967101), (-307329317090747761)⟩, true⟩

def state01 : KState := ⟨⟨362495004409547822, 362495135939215521⟩, ⟨(-939578394852436932), (-931309768804386448)⟩, true⟩

def words00 : List Nat := [371285132531741391, 371285132618830828, 371285132819916786, 371285133022397413, 371285133204394056, 371285133276682560, 371285133387361615, 371285133499653853, 371285133682928716, 371285133793724609]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 93100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 93100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490835411093638, 362490966970477052⟩, ⟨(-551342268125697033), (-543070875101265283)⟩, true⟩

def words01 : List Nat := [371285133893887061, 371285133995176729, 371285134210470779, 371285134386382472, 371285134566521266, 371285134747859773, 371285134927804398, 371285134954850838, 371285135019706646, 371285135086421885]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 93110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 93100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481362573918768, 362481494162347586⟩, ⟨330807072690196760, 339081170571375880⟩, true⟩

def words02 : List Nat := [371285135187083595, 371285135190342188, 371285135148458204, 371285135106274072, 371285135062871824, 371285135049267532, 371285135038351283, 371285135076820839, 371285135103572841, 371285135106947301]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 93120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 93100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498396904374914, 362498528522215053⟩, ⟨(-1255680663507056047), (-1247403826400279253)⟩, true⟩

def words03 : List Nat := [371285135146289971, 371285135226436240, 371285135420189853, 371285135461319545, 371285135473483863, 371285135486661916, 371285135557296097, 371285135589389676, 371285135735393114, 371285135882814572]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 93130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 93100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485131674788965, 362485263322097762⟩, ⟨(-20097852575716032), (-11818270611828780)⟩, true⟩

def words04 : List Nat := [371285136027299619, 371285136076750191, 371285136197694542, 371285136320350364, 371285136461630873, 371285136464890225, 371285136452676728, 371285136435855173, 371285136444786400, 371285136449915909]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 93140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 93100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481392378341901, 362481524055035826⟩, ⟨328288460409211311, 336570779747258473⟩, true⟩

def words05 : List Nat := [371285136568763679, 371285136688984298, 371285136807731270, 371285136810991909, 371285136809582587, 371285136825487472, 371285136923700958, 371285136926976411, 371285136915143885, 371285136880065316]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492716268605658, 362492847974506597⟩, ⟨(-726712061537687983), (-718427021123885319)⟩, true⟩

def words06 : List Nat := [371285136899063495, 371285136902656258, 371285136949137632, 371285136998733220, 371285137029161841, 371285137032423661, 371285136929266350, 371285136931205076, 371285137044558563, 371285137130777069]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491442449290963, 362491574184811664⟩, ⟨(-608008393439411820), (-599720593199291558)⟩, true⟩

def words07 : List Nat := [371285137215444318, 371285137301170155, 371285137468379204, 371285137586408488, 371285137738080384, 371285137891032719, 371285138000936877, 371285138004197262, 371285138029346883, 371285138102421485]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483482554970717, 362483614319533368⟩, ⟨133721830374761831, 142012336891262841⟩, true⟩

def words08 : List Nat := [371285138218441053, 371285138221701620, 371285138184417232, 371285138143261926, 371285138100730830, 371285138094704904, 371285138096651091, 371285138157621810, 371285138217186630, 371285138220562355]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496808477070999, 362496940271194215⟩, ⟨(-1108209586829120244), (-1099916325418132590)⟩, true⟩

def words09 : List Nat := [371285138238036160, 371285138273570760, 371285138394535428, 371285138398719831, 371285138401272345, 371285138397992667, 371285138446204388, 371285138461330522, 371285138590170416, 371285138720508942]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk931
