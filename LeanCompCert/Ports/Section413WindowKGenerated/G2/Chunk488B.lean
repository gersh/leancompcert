import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk488A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk488B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk488A

def state06 : KState := ⟨⟨360580125048385500, 360580139996684981⟩, ⟨92666994260147035, 93160525630379869⟩, true⟩

def words05 : List Nat := [360582053042297863, 360582052381330898, 360582051720195302, 360582051039231670, 360582050238115409, 360582049077504186, 360582047916811100, 360582047174012753, 360582046717882986, 360582046679567306]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577894787665178, 360577909742376412⟩, ⟨201500013643213683, 201993858322963529⟩, true⟩

def words06 : List Nat := [360582046641149845, 360582046344174431, 360582045988414419, 360582045956039091, 360582045923487423, 360582045686575920, 360582045171499904, 360582044319115652, 360582043466635959, 360582043031885784]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360548127915557983, 360548142876606724⟩, ⟨1656485474971403516, 1656979629397601534⟩, true⟩

def words07 : List Nat := [360582043280729030, 360582043614263381, 360582043626495315, 360582043653044471, 360582043653610800, 360582043348009562, 360582043042223822, 360582042979333478, 360582042498022227, 360582041805195055]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360566965696149661, 360566980663559067⟩, ⟨735580996771818836, 736075462139419488⟩, true⟩

def words08 : List Nat := [360582041112249698, 360582040410764396, 360582039920736612, 360582039848101317, 360582039775411882, 360582039343985493, 360582038494222290, 360582037660608479, 360582036826811642, 360582036410381310]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360550497361380129, 360550512335199466⟩, ⟨1540759182904528501, 1541253961685198475⟩, true⟩

def words09 : List Nat := [360582036103036231, 360582035540831651, 360582034978521915, 360582034540631448, 360582034358061952, 360582033787245768, 360582033216385483, 360582032435797345, 360582031464917661, 360582030821123499]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk488B
