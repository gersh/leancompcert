import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk401

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362513382162281001, 362513404984698945⟩, ⟨(-1129680527814669719), (-1129062108706109711)⟩, true⟩

def state01 : KState := ⟨⟨362477597813433584, 362477620647728078⟩, ⟨305336714429290670, 305955609848433886⟩, true⟩

def words00 : List Nat := [371285250228002414, 371285250229317135, 371285250104593532, 371285250073497758, 371285250122637104, 371285250123960795, 371285249649253517, 371285249135271850, 371285248620794501, 371285248561212208]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 40100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 40100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362459299404046880, 362459322250185453⟩, ⟨1039517908955462283, 1040137279500768955⟩, true⟩

def words01 : List Nat := [371285248802811356, 371285249235112914, 371285249666572368, 371285249667888721, 371285249403050291, 371285249304694866, 371285249205699772, 371285249174224803, 371285248549933149, 371285247905207905]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 40110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 40100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489848143562516, 362489871001480313⟩, ⟨(-186190040301551958), (-185570197115454668)⟩, true⟩

def words02 : List Nat := [371285247259914216, 371285247142770492, 371285246915642030, 371285247113461415, 371285247210646998, 371285247211962720, 371285246481809490, 371285246373071751, 371285246773925685, 371285246890515836]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 40120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 40100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483722195269127, 362483745065181696⟩, ⟨59716434169441437, 60336758765868935⟩, true⟩

def words03 : List Nat := [371285246911150638, 371285246932185419, 371285247464635025, 371285247687389492, 371285247971062798, 371285248255237132, 371285248460182952, 371285248461522489, 371285248258917704, 371285248223098136]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 40130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 40100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362469639025377265, 362469661907007078⟩, ⟨625094779035165218, 625715574022819212⟩, true⟩

def words04 : List Nat := [371285248712907362, 371285248714223659, 371285248414946330, 371285248116092882, 371285247816744074, 371285247501366466, 371285246875406836, 371285246703800419, 371285246531780356, 371285246354678880]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 40140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 40100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362506439952158429, 362506462845714708⟩, ⟨(-852566113377653687), (-851944839482117551)⟩, true⟩

def words05 : List Nat := [371285246199233897, 371285246432643305, 371285247285224458, 371285247506089097, 371285247625761086, 371285247745825062, 371285248275300111, 371285248549140211, 371285249078293639, 371285249608009419]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 40150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 40100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362507188196775928, 362507211102200697⟩, ⟨(-882736012423850839), (-882114261827712107)⟩, true⟩

def words06 : List Nat := [371285250016295705, 371285250017613046, 371285250023604632, 371285250337531233, 371285250769153945, 371285250814981399, 371285250860753889, 371285250906971041, 371285251572142456, 371285252120302619]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 40160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 40100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484212375110759, 362484235292407052⟩, ⟨40399555383783453, 41021782917067771⟩, true⟩

def words07 : List Nat := [371285253035594769, 371285253951372081, 371285254746584497, 371285254815373256, 371285255074332851, 371285255333963878, 371285256212204981, 371285256265634810, 371285256266620037, 371285256242703645]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 40170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 40100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485203320456202, 362485226249530763⟩, ⟨617969821896056, 1240670666824296⟩, true⟩

def words08 : List Nat := [371285256637342223, 371285256774331082, 371285257089716841, 371285257405623727, 371285257655013403, 371285257656331457, 371285257175459724, 371285256950815266, 371285257118300078, 371285257119664300]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 40180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 40100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362503333962819159, 362503356903920012⟩, ⟨(-728093501846800907), (-727470317606722415)⟩, true⟩

def words09 : List Nat := [371285257119881602, 371285257119947135, 371285257736954297, 371285258226257594, 371285258901739689, 371285259577687242, 371285260252670899, 371285260253989251, 371285260625716786, 371285261077507567]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 40190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 40100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 40100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk401
