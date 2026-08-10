import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk681A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk681A
