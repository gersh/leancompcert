import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk681

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360589111593073345, 360589141417630065⟩, ⟨(-431598591932220696), (-430226653159710550)⟩, true⟩

def state01 : KState := ⟨⟨360573112137246615, 360573141970879205⟩, ⟨657963382560997974, 659335939444962250⟩, true⟩

def words00 : List Nat := [360582823984824072, 360582823985789099, 360582823962128536, 360582823758290301, 360582823554301314, 360582823262176893, 360582823078266313, 360582822901409408, 360582822724452835, 360582822428072642]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583232069279316, 360583261911995981⟩, ⟨(-31315979793997752), (-29942804148663928)⟩, true⟩

def words01 : List Nat := [360582822359874819, 360582822434102352, 360582822723296716, 360582822797410503, 360582822798300106, 360582822691526115, 360582822584584942, 360582822410661888, 360582822351333099, 360582822358787005]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360567459550065630, 360567489401953259⟩, ⟨1043020709373424747, 1044394509789702877⟩, true⟩

def words02 : List Nat := [360582822359654384, 360582822235639035, 360582821896239210, 360582821581485079, 360582821266467771, 360582820888532028, 360582820413106081, 360582819830026880, 360582819246780469, 360582818838468593]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360564731047111320, 360564760908078625⟩, ⟨1228912571624293778, 1230286990684362608⟩, true⟩

def words03 : List Nat := [360582818614261143, 360582818385478915, 360582818156602507, 360582817792695763, 360582817494587751, 360582817142422243, 360582816789981924, 360582816591325847, 360582816455162800, 360582816191182300]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360609120212963544, 360609150083020175⟩, ⟨(-1795971419134326854), (-1794596380683824246)⟩, true⟩

def words04 : List Nat := [360582815926991369, 360582815963419906, 360582816213325971, 360582816463409096, 360582816480000618, 360582816480968369, 360582816604724430, 360582816774798787, 360582817046354140, 360582817433746007]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360579192553861103, 360579222433102099⟩, ⟨243794716439998642, 245170380850618308⟩, true⟩

def words05 : List Nat := [360582817713308950, 360582817992985529, 360582818243124902, 360582818634532859, 360582818932921345, 360582819231464387, 360582819421829852, 360582819467267316, 360582819468063817, 360582819416389227]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585628056249372, 360585657944557451⟩, ⟨(-194899486601303475), (-193523204131833399)⟩, true⟩

def words06 : List Nat := [360582819526579513, 360582819527542925, 360582819521143369, 360582819407202560, 360582819293108008, 360582819126411192, 360582819161381999, 360582819196531044, 360582819197390091, 360582819153808719]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606171866588637, 360606201764007338⟩, ⟨(-1595513922317767464), (-1594137018734073394)⟩, true⟩

def words07 : List Nat := [360582819411114961, 360582819668705152, 360582819921317818, 360582820017906961, 360582820018805769, 360582819923292373, 360582819891904479, 360582820119496816, 360582820463216468, 360582820807161090]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579812552350517, 360579842458940322⟩, ⟨201716745059166402, 203094273975298048⟩, true⟩

def words08 : List Nat := [360582821043367189, 360582821121424096, 360582821328145128, 360582821535152395, 360582821624497518, 360582821625461304, 360582821560618342, 360582821301988378, 360582821043186718, 360582820817555593]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360567252019854034, 360567281935520903⟩, ⟨1058273026739180355, 1059651174665455345⟩, true⟩

def words09 : List Nat := [360582820774660308, 360582820721262516, 360582820667769178, 360582820506470535, 360582820351826123, 360582820078714639, 360582819805328666, 360582819676765588, 360582819569592088, 360582819342774063]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk681
