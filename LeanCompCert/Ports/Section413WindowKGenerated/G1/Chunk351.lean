import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk351

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362522303143161490, 362522320439297961⟩, ⟨(-1311856401049673193), (-1311446100110920839)⟩, true⟩

def state01 : KState := ⟨⟨362488428173545071, 362488445479816231⟩, ⟨(-122679535456141676), (-122268878736239802)⟩, true⟩

def words00 : List Nat := [371284959844055871, 371284960240227232, 371284960633235826, 371284961026622129, 371284961269220683, 371284961270475896, 371284961758386867, 371284962408557567, 371284963026949359, 371284963127313134]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 35100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 35100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362511072921667591, 362511090238272417⟩, ⟨(-917784171067435043), (-917373151481566525)⟩, true⟩

def words01 : List Nat := [371284964037968361, 371284964949206819, 371284966218846927, 371284966514903211, 371284966679157319, 371284966843746509, 371284967818446331, 371284968388998644, 371284969133575033, 371284969878616327]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 35110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 35100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362504225548525508, 362504242875408916⟩, ⟨(-677405503457445315), (-676994122833575095)⟩, true⟩

def words02 : List Nat := [371284970568527569, 371284970569670906, 371284970599033761, 371284970763042143, 371284971175446431, 371284971176612147, 371284971123518051, 371284971067287272, 371284971763296762, 371284972313146710]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 35120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 35100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480084053778598, 362480101390943893⟩, ⟨170918043768780150, 171329785647313550⟩, true⟩

def words03 : List Nat := [371284973360648729, 371284974408542137, 371284975278342768, 371284975427486265, 371284975826467927, 371284976226019018, 371284977233277071, 371284977234417926, 371284977162600442, 371284977025139890]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 35130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 35100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362501547133883913, 362501564481244602⟩, ⟨(-583314907414003658), (-582902807217112830)⟩, true⟩

def words04 : List Nat := [371284977557972244, 371284977827360603, 371284978836815955, 371284979846689109, 371284980614546633, 371284980615687808, 371284980327917772, 371284980352387580, 371284981185401272, 371284981658359987]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 35140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 35100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362517118414933430, 362517135772707689⟩, ⟨(-1130676328561112848), (-1130263862275881476)⟩, true⟩

def words05 : List Nat := [371284982127940692, 371284982597900321, 371284983876300332, 371284984891064995, 371284986078505963, 371284987266317448, 371284988450732572, 371284988557498697, 371284989472585507, 371284990388268229]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 35150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 35100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471292328995924, 362471309696947652⟩, ⟨480822415122322291, 481235239300771177⟩, true⟩

def words06 : List Nat := [371284991638029652, 371284991810444968, 371284991984335052, 371284992158582439, 371284992470159472, 371284992471416821, 371284992532400590, 371284992685221209, 371284992813175628, 371284992814357399]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 35160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 35100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362516006329433116, 362516023707689571⟩, ⟨(-1091999613850440013), (-1091586427202057685)⟩, true⟩

def words07 : List Nat := [371284992845337339, 371284993265929213, 371284994190346023, 371284994191488465, 371284994189312775, 371284993943262237, 371284994045637504, 371284994215685246, 371284995098481330, 371284995981723793]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 35170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 35100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485204111960542, 362485221500544850⟩, ⟨(-8193162312463474), (-7779612278412714)⟩, true⟩

def words08 : List Nat := [371284996861162269, 371284997083458480, 371284998002634404, 371284998922363796, 371285000001985627, 371285000134350975, 371285000198675609, 371285000263373849, 371285000424707444, 371285000432309267]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 35180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 35100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362460358889429238, 362460376288311225⟩, ⟨866337446034011850, 866751358494922844⟩, true⟩

def words09 : List Nat := [371285000972098735, 371285001512328500, 371285002048846626, 371285002049989368, 371285001510751848, 371285001220787910, 371285001304161559, 371285001305304466, 371285000604694646, 371284999906450286]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 35190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 35100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 35100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk351
