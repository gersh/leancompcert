import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk947

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497332613502257, 362497468852275465⟩, ⟨(-1172040968680951119), (-1163330122558433627)⟩, true⟩

def state01 : KState := ⟨⟨362482040404206225, 362482176672950757⟩, ⟨276150871488004479, 284864556045887275⟩, true⟩

def words00 : List Nat := [371285184740864283, 371285184744181904, 371285184745070338, 371285184766937256, 371285184803036119, 371285184806353919, 371285184693995653, 371285184568741313, 371285184442168518, 371285184428795398]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 94700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 94700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479050671559529, 362479186970188371⟩, ⟨559369682188506407, 568086197239115943⟩, true⟩

def words01 : List Nat := [371285184463502473, 371285184531345829, 371285184595410976, 371285184598737799, 371285184573208541, 371285184574925443, 371285184618557069, 371285184621891702, 371285184561370558, 371285184501831521]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 94710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 94700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485606366257125, 362485742694557428⟩, ⟨(-61606003795454491), (-52886678109262105)⟩, true⟩

def words02 : List Nat := [371285184440779532, 371285184428799195, 371285184400173224, 371285184444148172, 371285184469186658, 371285184472505662, 371285184348633991, 371285184338046323, 371285184402531438, 371285184411861064]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 94720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 94700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493183026278685, 362493319384829989⟩, ⟨(-779391713554804432), (-770669522038529626)⟩, true⟩

def words03 : List Nat := [371285184414396976, 371285184403326456, 371285184471042561, 371285184514372492, 371285184589968837, 371285184666882337, 371285184733235668, 371285184736613831, 371285184806951972, 371285184896888776]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 94730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 94700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483477296071577, 362483613684150470⟩, ⟨140174561872483294, 148899550987965546⟩, true⟩

def words04 : List Nat := [371285185055301644, 371285185078224035, 371285185080750002, 371285185075928105, 371285185069827796, 371285185070726948, 371285185067850800, 371285185124598727, 371285185179928119, 371285185183369341]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 94740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 94700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362495049439634858, 362495185857828185⟩, ⟨(-956321730714563271), (-947593888114116489)⟩, true⟩

def words05 : List Nat := [371285185237175296, 371285185309445446, 371285185461485845, 371285185532706388, 371285185586169007, 371285185640634846, 371285185747694867, 371285185810739367, 371285185918560137, 371285186027854735]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 94750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 94700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489753405060862, 362489889853224298⟩, ⟨(-454484254961524972), (-445753572243188350)⟩, true⟩

def words06 : List Nat := [371285186136331426, 371285186139651786, 371285186162464811, 371285186229440408, 371285186300886277, 371285186304265808, 371285186284177743, 371285186266611863, 371285186319017663, 371285186372494506]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 94760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 94700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481033096610853, 362481169574670472⟩, ⟨372025126966501433, 380758643098871589⟩, true⟩

def words07 : List Nat := [371285186535789545, 371285186700415850, 371285186842422393, 371285186845743166, 371285186839151961, 371285186837318178, 371285186939242077, 371285186942562890, 371285186902204068, 371285186863582678]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 94770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 94700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481088264680272, 362481224772433289⟩, ⟨366830219016577103, 375566549645484203⟩, true⟩

def words08 : List Nat := [371285186892458969, 371285186909641657, 371285186972602312, 371285187036947916, 371285187078745837, 371285187082067353, 371285186988824382, 371285186910454164, 371285186859401436, 371285186862839930]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 94780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 94700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492175877257005, 362492312415321523⟩, ⟨(-684218706645223508), (-675479502643004420)⟩, true⟩

def words09 : List Nat := [371285186823529139, 371285186783101440, 371285186808587907, 371285186841636803, 371285186906870686, 371285186973363486, 371285187037736216, 371285187041083399, 371285187099944447, 371285187179272927]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 94790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 94700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 94700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk947
