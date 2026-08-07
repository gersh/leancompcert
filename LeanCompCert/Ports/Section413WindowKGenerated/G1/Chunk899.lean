import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk899

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490516033251236, 362490638318212610⟩, ⟨(-503171054361812524), (-495748459631621418)⟩, true⟩

def state01 : KState := ⟨⟨362476303206046003, 362476425519378667⟩, ⟨774578182235002854, 782003327685318988⟩, true⟩

def words00 : List Nat := [371285123973338637, 371285123976475283, 371285123863276421, 371285123814832567, 371285123764795503, 371285123753516418, 371285123576596825, 371285123391200810, 371285123204477628, 371285123142865324]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 89900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 89900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362470376734292932, 362470499075861538⟩, ⟨1307506099893535670, 1314933784181086310⟩, true⟩

def words01 : List Nat := [371285123056360799, 371285123067896240, 371285123070249044, 371285123052943730, 371285122943856335, 371285122840393041, 371285122751749091, 371285122754885901, 371285122608853318, 371285122449795937]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 89910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 89900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473395651820272, 362473518021509456⟩, ⟨1036076833443357517, 1043507046477644515⟩, true⟩

def words02 : List Nat := [371285122289308687, 371285122212522559, 371285122089002061, 371285122090304288, 371285122090677626, 371285122057782935, 371285121859103010, 371285121753175137, 371285121645598044, 371285121569229657]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 89920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 89900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480034416502057, 362480156814735889⟩, ⟨439030991316634476, 446463771516440108⟩, true⟩

def words03 : List Nat := [371285121442549173, 371285121316815751, 371285121189836486, 371285121179363003, 371285121121057038, 371285121101889549, 371285121081561505, 371285121060589501, 371285120883994664, 371285120832653573]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 89930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 89900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362467646500219228, 362467768926430701⟩, ⟨1553276104868455544, 1560711401523558076⟩, true⟩

def words04 : List Nat := [371285120831185116, 371285120834322717, 371285120723582879, 371285120590209698, 371285120455609307, 371285120360120332, 371285120216789531, 371285120079465881, 371285119941113638, 371285119803601614]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 89940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 89900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483686256148303, 362483808710741458⟩, ⟨110417814108165516, 117855663836115804⟩, true⟩

def words05 : List Nat := [371285119612836987, 371285119540337544, 371285119478530093, 371285119481669374, 371285119353007164, 371285119204567276, 371285119054917907, 371285118947272611, 371285118811370639, 371285118800379477]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472483338228353, 362472605821138678⟩, ⟨1118275552442205910, 1125715949725169868⟩, true⟩

def words06 : List Nat := [371285118788162551, 371285118774024866, 371285118618969212, 371285118589085983, 371285118557574116, 371285118554784848, 371285118386569536, 371285118219328576, 371285118050786938, 371285117946844193]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362465016269732182, 362465138780892604⟩, ⟨1790133189331798321, 1797576128421872657⟩, true⟩

def words07 : List Nat := [371285117809941533, 371285117725513381, 371285117640088533, 371285117553793835, 371285117301969878, 371285117068095314, 371285116832564164, 371285116721517600, 371285116506935312, 371285116288432301]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473836712006317, 362473959251243286⟩, ⟨996435467448773581, 1003880933010353027⟩, true⟩

def words08 : List Nat := [371285116068548230, 371285115906627168, 371285115681450563, 371285115581018382, 371285115479598750, 371285115347744063, 371285115096537322, 371285114931689004, 371285114765250018, 371285114723329189]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362466240259934551, 362466362827882255⟩, ⟨1680110038177245950, 1687558087555714656⟩, true⟩

def words09 : List Nat := [371285114601754594, 371285114450195740, 371285114297275921, 371285114250006792, 371285114147202793, 371285114065665932, 371285113983098769, 371285113893990589, 371285113677666251, 371285113473299541]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk899
