import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk172

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360544552938615981, 360544554632416143⟩, ⟨672263630000701366, 672283351420880372⟩, true⟩

def state01 : KState := ⟨⟨360759203080029255, 360759204775885044⟩, ⟨(-3020827917001958028), (-3020808160214874196)⟩, true⟩

def words00 : List Nat := [360583638631407552, 360583640850180960, 360583646435502907, 360583652020219408, 360583654514429654, 360583657132331972, 360583663115350791, 360583669097739823, 360583678444444292, 360583688643166732]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 17200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 17200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360678301592610198, 360678303290544188⟩, ⟨(-1628111050430767150), (-1628091257867467114)⟩, true⟩

def words01 : List Nat := [360583697145066739, 360583705646003713, 360583714055599335, 360583724635201696, 360583732979950879, 360583741323765007, 360583747965602974, 360583751268634914, 360583756759637364, 360583762250078044]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 17210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 17200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604758332685248, 360604760032673289⟩, ⟨(-361387201862007670), (-361367373917876754)⟩, true⟩

def words02 : List Nat := [360583768810265136, 360583773173418700, 360583775843689734, 360583778513674569, 360583779049852395, 360583782391960720, 360583784452437234, 360583786512712983, 360583786882481319, 360583788099882513]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 17220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 17200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360748139393796254, 360748141095843881⟩, ⟨(-2832655692742310162), (-2832635829301131424)⟩, true⟩

def words03 : List Nat := [360583792672621467, 360583797244893202, 360583803213995529, 360583809299903790, 360583812494676589, 360583815689094204, 360583819361848931, 360583825541795454, 360583835073036776, 360583844603221578]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 17230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 17200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360697320512280827, 360697322216409826⟩, ⟨(-1956787084586922361), (-1956767185252602509)⟩, true⟩

def words04 : List Nat := [360583851496023432, 360583856669151891, 360583863868948718, 360583871067976157, 360583877387299299, 360583880380769859, 360583881688516914, 360583882996141392, 360583886437305362, 360583893013160589]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 17240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 17200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360521989975140932, 360521991681326780⟩, ⟨1068718808640637236, 1068738743466138386⟩, true⟩

def words05 : List Nat := [360583900561649730, 360583908109305104, 360583913730138870, 360583916027491523, 360583916027678301, 360583914989947363, 360583916258278679, 360583916258497281, 360583915242342048, 360583911654876383]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 17250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 17200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360627075527735052, 360627077235987974⟩, ⟨(-745470032011893092), (-745450061498429422)⟩, true⟩

def words06 : List Nat := [360583908067777347, 360583907213532040, 360583910360835319, 360583913507816641, 360583913805298803, 360583913805517572, 360583912399047927, 360583912635648076, 360583912785181211, 360583915284653458]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 17260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 17200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360590230147057114, 360590231857394619⟩, ⟨(-108993712406099765), (-108973705881324243)⟩, true⟩

def words07 : List Nat := [360583915571315036, 360583915857965699, 360583917640227451, 360583921083649925, 360583923656648328, 360583926229387933, 360583926658574641, 360583926658793596, 360583925508423053, 360583925873604253]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 17270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 17200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567098241614847, 360567099954017864⟩, ⟨290408892693928473, 290428934920920587⟩, true⟩

def words08 : List Nat := [360583926718498574, 360583926718717529, 360583924251396786, 360583919164295531, 360583914077747174, 360583908119541307, 360583904425358336, 360583902872648797, 360583901320097293, 360583897463267195]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 17280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 17200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360661169634568037, 360661171349037595⟩, ⟨(-1336585116706725498), (-1336565038738940094)⟩, true⟩

def words09 : List Nat := [360583898849382023, 360583901206749193, 360583906892139737, 360583909268537180, 360583909268739155, 360583908810661397, 360583908352597564, 360583908787864393, 360583913254085804, 360583917719840501]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 17290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 17200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 17200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk172
