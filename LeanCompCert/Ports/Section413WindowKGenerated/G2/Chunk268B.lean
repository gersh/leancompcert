import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk268A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk268B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk268A

def state06 : KState := ⟨⟨360515589288379380, 360515593586479181⟩, ⟨1797536394868351287, 1797614484824064621⟩, true⟩

def words05 : List Nat := [360582529801002331, 360582529885898256, 360582529886212766, 360582529272542982, 360582527947228264, 360582525900771309, 360582523854360258, 360582522829036580, 360582521412347145, 360582518920984917]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360667811801054178, 360667816102484693⟩, ⟨(-2291820029671140903), (-2291741850235971955)⟩, true⟩

def words06 : List Nat := [360582516429727677, 360582515405700777, 360582516872816471, 360582518339890816, 360582518665759055, 360582519582541672, 360582521443132865, 360582523303688599, 360582526118857895, 360582529293276403]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611963648898681, 360611967953696846⟩, ⟨(-791045632093251038), (-790967362152386574)⟩, true⟩

def words07 : List Nat := [360582531531536743, 360582533769667378, 360582535243706716, 360582537418277683, 360582539036381284, 360582540654421470, 360582541275657129, 360582541276010321, 360582542084160011, 360582543179240822]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566510470490585, 360566514778613190⟩, ⟨430986892107386184, 431065251426118746⟩, true⟩

def words08 : List Nat := [360582545655635262, 360582546753750028, 360582546942165533, 360582547130606357, 360582547130902739, 360582546935432064, 360582546935723255, 360582546678894355, 360582546422046186, 360582545468513753]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360669994067517452, 360669998378975845⟩, ⟨(-2352125019726470393), (-2352046570691989639)⟩, true⟩

def words09 : List Nat := [360582545657256012, 360582546442182875, 360582548607525552, 360582551400465926, 360582552792624259, 360582554184704634, 360582555970795045, 360582558452278215, 360582561703119299, 360582564953798641]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk268B
