import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk032

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362622761177831395, 362622761293139151⟩, ⟨(-436062985730422097), (-436062735353524175)⟩, true⟩

def state01 : KState := ⟨⟨362508400445520797, 362508400561590234⟩, ⟨(-71113508124413974), (-71113255306141612)⟩, true⟩

def words00 : List Nat := [371286549865160983, 371286549865245564, 371286436757270793, 371286419979130993, 371286415489122965, 371286415489209016, 371286348794284752, 371286282821721523, 371286246899404863, 371286253798804142]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 3200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 3200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362095696354325562, 362095696471159620⟩, ⟨1256554601997922021, 1256554857274544015⟩, true⟩

def words01 : List Nat := [371286307145332685, 371286360458688164, 371286385394769888, 371286385394854823, 371286282553344236, 371286209071730525, 371286157613999842, 371286157614084837, 371286052127253190, 371285930898884634]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 3210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 3200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362277084404871943, 362277084522467101⟩, ⟨672182014489518142, 672182272220834892⟩, true⟩

def words02 : List Nat := [371285809745751684, 371285783862040195, 371285711819932343, 371285689631355694, 371285667456511930, 371285630565344013, 371285466845059225, 371285343104189753, 371285219439921181, 371285190489098939]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 3220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 3200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362319373910383957, 362319374028758077⟩, ⟨536094700899550566, 536094961150818776⟩, true⟩

def words03 : List Nat := [371285126080012374, 371285059899676233, 371284998985570849, 371284998985666860, 371284987575996175, 371284996675010174, 371285004537774784, 371285004537860353, 371284886520516135, 371284835436520676]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 3230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 3200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361872995354968852, 361872995474107148⟩, ⟨1984330956883856398, 1984331219615046550⟩, true⟩

def words04 : List Nat := [371284784384001105, 371284773257843914, 371284636645418507, 371284489084409621, 371284341614316091, 371284188276863797, 371283987988932637, 371283845797001972, 371283703692570260, 371283558926296394]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 3240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 3200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362479650330542457, 362479650450455069⟩, ⟨9711575045959273, 9711840297691895⟩, true⟩

def words05 : List Nat := [371283371118464262, 371283276625310341, 371283182190209611, 371283180955845338, 371283055055191440, 371282913740719054, 371282772512986613, 371282724274704692, 371282630456587675, 371282629542570926]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 3250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 3200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362216290138485799, 362216290259176926⟩, ⟨869479786823419845, 869480054617090785⟩, true⟩

def words06 : List Nat := [371282628629083600, 371282628335819244, 371282551189632590, 371282533553900219, 371282527589545255, 371282527589631679, 371282445739723044, 371282346031577181, 371282246384400357, 371282186300344233]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 3260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 3200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362157392265993993, 362157392387465105⟩, ⟨1063516691525845668, 1063516961873993110⟩, true⟩

def words07 : List Nat := [371282115848521647, 371282126679027591, 371282138401256932, 371282138401343536, 371282027030227798, 371281940286234165, 371281853595135454, 371281834302280599, 371281734248261729, 371281635363646201]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 3270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 3200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362091410971110538, 362091411093358913⟩, ⟨1281014011597927023, 1281014284499533097⟩, true⟩

def words08 : List Nat := [371281536539268859, 371281495581529802, 371281408196257910, 371281350426353898, 371281292691596297, 371281224057515201, 371281060303967352, 371280961614912291, 371280862985824579, 371280777137279744]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 3280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 3200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362195665789421692, 362195665912462219⟩, ⟨937629493622758876, 937629769134579672⟩, true⟩

def words09 : List Nat := [371280658824964468, 371280541883181835, 371280425012389465, 371280373037172455, 371280277875400151, 371280212021708308, 371280146207934916, 371280058846018703, 371279882271595567, 371279796145533304]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 3290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 3200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 3200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk032
