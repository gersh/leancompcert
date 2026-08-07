import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk427

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478391618287923, 362478417628261292⟩, ⟨290973537691773788, 291723968894122004⟩, true⟩

def state01 : KState := ⟨⟨362506317242038602, 362506343264596839⟩, ⟨(-901485567566370383), (-900734598924584587)⟩, true⟩

def words00 : List Nat := [371285249801507239, 371285250000344339, 371285250747737007, 371285251495688848, 371285252218586696, 371285252285750525, 371285252578958791, 371285252872849573, 371285253715049936, 371285254210280046]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 42700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 42700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362519864054887571, 362519890090291113⟩, ⟨(-1480169009713768414), (-1479417492386418288)⟩, true⟩

def words01 : List Nat := [371285254666278892, 371285255122745226, 371285255841606226, 371285256381055844, 371285257083115102, 371285257785667475, 371285258454365415, 371285258717633694, 371285259529248699, 371285260341633863]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 42710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 42700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362498693364325832, 362498719412276071⟩, ⟨(-575682737517271286), (-574930684129634908)⟩, true⟩

def words02 : List Nat := [371285261241182010, 371285261508302358, 371285261726224723, 371285261944598888, 371285262333771618, 371285262450958871, 371285263116235454, 371285263782092460, 371285264445123942, 371285264761457471]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 42720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 42700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362530125958822864, 362530152019486934⟩, ⟨(-1918995858707344463), (-1918243261992519487)⟩, true⟩

def words03 : List Nat := [371285265329133887, 371285265897505764, 371285266955727097, 371285267428505435, 371285267672746182, 371285267917404912, 371285268709941988, 371285269280772699, 371285270331863257, 371285271383516964]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 42730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 42700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362532114257872011, 362532140331277021⟩, ⟨(-2003984646047278578), (-2003231504721489442)⟩, true⟩

def words04 : List Nat := [371285272435501277, 371285273110948470, 371285274334186410, 371285275558116188, 371285276914953305, 371285277916378496, 371285278915153583, 371285279914344321, 371285281113165397, 371285282210888692]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 42740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 42700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498507614393470, 362498533700496976⟩, ⟨(-566983571996508845), (-566229887744527561)⟩, true⟩

def words05 : List Nat := [371285283856019116, 371285285501665053, 371285287144543877, 371285288058278273, 371285289023714499, 371285289989811739, 371285291030424580, 371285291342129176, 371285291652883244, 371285291964154409]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 42750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 42700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362511093028789221, 362511119127535192⟩, ⟨(-1105202910306534023), (-1104448685400258297)⟩, true⟩

def words06 : List Nat := [371285292736728244, 371285293237766319, 371285293835249790, 371285294433248156, 371285294951828886, 371285294953238637, 371285295078784550, 371285295416661715, 371285296149999222, 371285296755240875]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 42760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 42700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502338687290208, 362502364798849378⟩, ⟨(-730656526796738658), (-729901753805373488)⟩, true⟩

def words07 : List Nat := [371285297348084990, 371285297941368702, 371285299081656972, 371285299950662099, 371285300860000126, 371285301769844908, 371285302525106716, 371285302645241597, 371285303045040067, 371285303445589628]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 42770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 42700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362498259782950337, 362498285907079350⟩, ⟨(-556130232143027567), (-555374921348777603)⟩, true⟩

def words08 : List Nat := [371285304329179472, 371285304484692960, 371285304644617921, 371285304805052557, 371285305111028479, 371285305145495089, 371285305726615882, 371285306308273043, 371285306823549358, 371285307128332680]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 42780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 42700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362531643085980345, 362531669222881807⟩, ⟨(-1984817223752635639), (-1984061366359979833)⟩, true⟩

def words09 : List Nat := [371285307657626540, 371285308187621061, 371285309263970329, 371285309612586049, 371285309876003726, 371285310139831217, 371285310950106478, 371285311563215545, 371285312647296156, 371285313731973652]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 42790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 42700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 42700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk427
