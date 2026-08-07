import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk488

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586166677948161, 360586181588063417⟩, ⟨(-201046503699116209), (-200554836861244353)⟩, true⟩

def state01 : KState := ⟨⟨360580718754715684, 360580733671230586⟩, ⟨64685786320704641, 65177765492559213⟩, true⟩

def words00 : List Nat := [360582071942612591, 360582071818571684, 360582071574257995, 360582071573179178, 360582071571909704, 360582071371951943, 360582070981628571, 360582070184117216, 360582069386509826, 360582069007544714]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360550609353377288, 360550624276230620⟩, ⟨1534370093020105358, 1534862381602837400⟩, true⟩

def words01 : List Nat := [360582068980741504, 360582068804824857, 360582068628842156, 360582068208240129, 360582067368232182, 360582066295148706, 360582065221904577, 360582064567156292, 360582064132590361, 360582063489290900]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585517880815926, 360585532810015657⟩, ⟨(-169920997728873018), (-169428399284852070)⟩, true⟩

def words02 : List Nat := [360582062845865501, 360582062642286184, 360582063082434355, 360582063522695125, 360582063589947683, 360582063590620163, 360582063238578874, 360582063211075508, 360582063183377142, 360582063120693611]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558392557614367, 360558407493223289⟩, ⟨1154817283417003017, 1155310194853498547⟩, true⟩

def words03 : List Nat := [360582063121292933, 360582062925851737, 360582062818971836, 360582063118171804, 360582063312501103, 360582063506932831, 360582063507532077, 360582063451696881, 360582062976691982, 360582062493117915]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360546585186869611, 360546600128809007⟩, ⟨1731417029443114790, 1731910250091879458⟩, true⟩

def words04 : List Nat := [360582062009339156, 360582061463400221, 360582060498398146, 360582059285478274, 360582058072498314, 360582056755216063, 360582055759284387, 360582055181317365, 360582054603301431, 360582053767500755]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk488
