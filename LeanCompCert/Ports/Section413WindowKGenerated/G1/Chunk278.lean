import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk278

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362522447794766571, 362522458435298991⟩, ⟨(-1036930403827320620), (-1036730437989508714)⟩, true⟩

def state01 : KState := ⟨⟨362496119470447998, 362496130118982799⟩, ⟨(-304991063696727232), (-304790875352062478)⟩, true⟩

def words00 : List Nat := [371285168657159761, 371285168658045487, 371285169188276916, 371285170099689374, 371285171312371023, 371285171313256935, 371285170804011892, 371285170226124041, 371285170359769583, 371285170754869605]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 27800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 27800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362465407739415068, 362465418395929568⟩, ⟨549281191040951068, 549481601341791470⟩, true⟩

def words01 : List Nat := [371285171409379170, 371285172064184267, 371285172711893916, 371285172712780114, 371285171639389664, 371285170957748828, 371285170883088985, 371285170883990487, 371285170420580696, 371285169711578087]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 27810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 27800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362504957234002975, 362504967898449411⟩, ⟨(-551107943621095590), (-550907312613348132)⟩, true⟩

def words02 : List Nat := [371285169359415421, 371285169360391761, 371285170077048472, 371285171080766554, 371285171791190030, 371285171792076571, 371285171062233619, 371285171342696092, 371285172449712327, 371285173161910539]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 27820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 27800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483964035472047, 362483974708011373⟩, ⟨33369454268958932, 33570310541553910⟩, true⟩

def words03 : List Nat := [371285173873102561, 371285174584566287, 371285176146797586, 371285177065749583, 371285178304772685, 371285179544035729, 371285180780781584, 371285180781669063, 371285180580334625, 371285180538131401]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 27830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 27800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362469990238006681, 362470000918447038⟩, ⟨422450001069951071, 422651077348153601⟩, true⟩

def words04 : List Nat := [371285181110057161, 371285181110944087, 371285180008684572, 371285178906209973, 371285177803484320, 371285177091424400, 371285176351085563, 371285176625191983, 371285176898761436, 371285176899680365]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 27840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 27800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362508856735534588, 362508867423996513⟩, ⟨(-660156119850216188), (-659954820129845670)⟩, true⟩

def words05 : List Nat := [371285177097358654, 371285177840337722, 371285178887841132, 371285178888730236, 371285178617560631, 371285178145288494, 371285178315196488, 371285178316173838, 371285179166705906, 371285180017940383]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 27850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 27800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362433201387425401, 362433212083886484⟩, ⟨1447851324141623723, 1448052846759653995⟩, true⟩

def words06 : List Nat := [371285180731854684, 371285180732742214, 371285179731546837, 371285178963377125, 371285178194806557, 371285177816742087, 371285175723981069, 371285173375773705, 371285171027384279, 371285169487788876]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 27860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 27800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362437463216326637, 362437473920795663⟩, ⟨1329209549247197806, 1329411295086542440⟩, true⟩

def words07 : List Nat := [371285167624182050, 371285166805602931, 371285165986774902, 371285165082372865, 371285163477437668, 371285162180362282, 371285160882929980, 371285160672014636, 371285158962116599, 371285157252757161]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 27870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 27800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362461200902414518, 362461211614846603⟩, ⟨667317457811628887, 667519425701341649⟩, true⟩

def words08 : List Nat := [371285155543126497, 371285154326163100, 371285152470026798, 371285151898084970, 371285151325924609, 371285150465882854, 371285148116886467, 371285146888759567, 371285145660232118, 371285145620787849]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 27880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 27800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476491921712582, 362476502642236848⟩, ⟨240809831718594249, 241012025339552011⟩, true⟩

def words09 : List Nat := [371285144763333059, 371285143908413278, 371285143480348171, 371285143481326830, 371285143267841602, 371285143106050195, 371285142943959256, 371285142592442775, 371285141374614662, 371285141066084144]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 27890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 27800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 27800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk278
