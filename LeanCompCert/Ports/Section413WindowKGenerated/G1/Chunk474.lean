import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk474

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477278821781546, 362477311146274400⟩, ⟨378748245329040551, 379783425889073129⟩, true⟩

def state01 : KState := ⟨⟨362476069881829173, 362476102220351658⟩, ⟨436061304241125610, 437097149879874830⟩, true⟩

def words00 : List Nat := [371285323523296689, 371285323524872701, 371285323226886935, 371285322878099945, 371285322528712783, 371285322282122439, 371285321811585232, 371285321785480818, 371285321758826203, 371285321734164775]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 47400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 47400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500380156393774, 362500412509155563⟩, ⟨(-716693596854851227), (-715657076057209151)⟩, true⟩

def words01 : List Nat := [371285321540799241, 371285321451999903, 371285321556309977, 371285321557886452, 371285321211128681, 371285320803308165, 371285320428900447, 371285320430667436, 371285320624733300, 371285320944741966]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 47410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 47400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480953763113838, 362480986130119562⟩, ⟨204517857762655422, 205555054076411482⟩, true⟩

def words02 : List Nat := [371285321185668088, 371285321187244943, 371285320964890389, 371285321040619443, 371285321136245240, 371285321137824354, 371285320756830890, 371285320378037716, 371285319998634858, 371285319991685584]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 47420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 47400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362455781571285169, 362455813952522419⟩, ⟨1398699488966881899, 1399737360353479433⟩, true⟩

def words03 : List Nat := [371285320253316502, 371285320607000655, 371285320901566597, 371285320903144508, 371285320686298746, 371285320572244880, 371285320521889523, 371285320523466837, 371285319997661236, 371285319377487712]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 47430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 47400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471018617321089, 362471051012679336⟩, ⟨675814716617880988, 676853257977221596⟩, true⟩

def words04 : List Nat := [371285318756619115, 371285318579621548, 371285318178971487, 371285317904409972, 371285317629382933, 371285317279471915, 371285316559849420, 371285316125483070, 371285315690289457, 371285315570276327]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 47440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 47400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362475092342687301, 362475124752414401⟩, ⟨482497418289877754, 483536641524871226⟩, true⟩

def words05 : List Nat := [371285315270839761, 371285314973504601, 371285314675574486, 371285314564074451, 371285314300622150, 371285314174723958, 371285314048288726, 371285313919972643, 371285313263509729, 371285313050803042]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 47450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 47400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362459240669003381, 362459273092776600⟩, ⟨1234947136068273354, 1235987026005940392⟩, true⟩

def words06 : List Nat := [371285312992114141, 371285312993695719, 371285312691143531, 371285312382095763, 371285312072446985, 371285311779517061, 371285311273800418, 371285310954467213, 371285310634630059, 371285310316834025]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 47460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 47400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499206104230043, 362499238542289660⟩, ⟨(-662418471445441584), (-661377903261659102)⟩, true⟩

def words07 : List Nat := [371285309769419143, 371285309566399541, 371285309493574970, 371285309495180946, 371285309258451152, 371285308945714839, 371285308730734385, 371285308732474539, 371285308930071662, 371285309225231013]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 47470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 47400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362465931500464836, 362465963952792194⟩, ⟨917562055528489499, 918603301217011393⟩, true⟩

def words08 : List Nat := [371285309386100035, 371285309387678970, 371285308958072573, 371285308922813942, 371285308986526156, 371285308988105168, 371285308498827390, 371285307918469913, 371285307337448052, 371285307041889205]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 47480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 47400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362462166035793535, 362462198502311571⟩, ⟨1096463939026413805, 1097505858703183051⟩, true⟩

def words09 : List Nat := [371285306670486263, 371285306707010148, 371285306745733468, 371285306747312753, 371285306195939037, 371285305589980819, 371285304983217640, 371285304818992300, 371285304373485403, 371285303888810586]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 47490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 47400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 47400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk474
