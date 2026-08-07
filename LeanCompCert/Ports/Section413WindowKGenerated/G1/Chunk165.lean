import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk165

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362509358963510735, 362509362547069676⟩, ⟨(-397941291861892787), (-397901295574101011)⟩, true⟩

def state01 : KState := ⟨⟨362491327830153879, 362491331418196042⟩, ⟨(-100293957499802433), (-100253887215116605)⟩, true⟩

def words00 : List Nat := [371285252848236771, 371285252848740846, 371285252767711005, 371285252668539198, 371285253542544420, 371285253543113625, 371285255200111362, 371285257161088474, 371285259104697229, 371285259472994957]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 16500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 16500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362543320736978562, 362543324329585191⟩, ⟨(-959163359796873669), (-959123214130102589)⟩, true⟩

def words01 : List Nat := [371285260953265295, 371285262433620307, 371285265306786494, 371285265307291378, 371285264299442152, 371285262642178616, 371285262657824674, 371285262658379711, 371285266023065136, 371285269537857687]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 16510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 16500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494100685193819, 362494104282350621⟩, ⟨(-146018149788884612), (-145977928930305352)⟩, true⟩

def words02 : List Nat := [371285273036020690, 371285273285130816, 371285275009000360, 371285276732921190, 371285279623494767, 371285279623999249, 371285277639794352, 371285274936406251, 371285273191094841, 371285273725885174]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 16520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 16500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362452251942937466, 362452255544631093⟩, ⟨546261203012769058, 546301498888720116⟩, true⟩

def words03 : List Nat := [371285277263366697, 371285280800620067, 371285283533120675, 371285283533634198, 371285284032814128, 371285284817398206, 371285288168306889, 371285288168811899, 371285286652291462, 371285284655809372]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 16530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 16500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362439542296376695, 362439545902600197⟩, ⟨756646698840501103, 756687069663690671⟩, true⟩

def words04 : List Nat := [371285282659356825, 371285281262222824, 371285278052021669, 371285277871800874, 371285277691434500, 371285276994040075, 371285271433864785, 371285269527493641, 371285267621090460, 371285267175691659]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 16540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 16500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362446063131385818, 362446066742219035⟩, ⟨648798407828554647, 648838854965428109⟩, true⟩

def words05 : List Nat := [371285264413625675, 371285261621301239, 371285259687947386, 371285259688504222, 371285259011567007, 371285257733832083, 371285256456086049, 371285255162092810, 371285250198007144, 371285247832494726]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 16550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 16500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477023268937912, 362477026884280569⟩, ⟨136216516278467839, 136257038115250661⟩, true⟩

def words06 : List Nat := [371285246748375036, 371285246748892000, 371285245860062326, 371285244956088606, 371285244216703316, 371285244217263875, 371285245659491150, 371285248202687879, 371285250000118749, 371285250000642383]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 16560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 16500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362545376939078410, 362545380558991133⟩, ⟨(-996664546256275061), (-996623948670452601)⟩, true⟩

def words07 : List Nat := [371285252029140021, 371285254553823489, 371285260719443976, 371285262037919679, 371285262867306792, 371285263696764399, 371285266198614258, 371285266923445438, 371285270549461027, 371285274175258521]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 16570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 16500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362444591560403958, 362444595184889450⟩, ⟨674595141826748677, 674635815252506465⟩, true⟩

def words08 : List Nat := [371285277788327542, 371285277788833878, 371285276560056506, 371285276118305646, 371285276120965929, 371285276121472388, 371285271726888232, 371285266936622818, 371285262146727922, 371285260393765430]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 16580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 16500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362375743572250535, 362375747201299375⟩, ⟨1817443166634180767, 1817483915789222291⟩, true⟩

def words09 : List Nat := [371285258436284980, 371285258929998444, 371285259413538241, 371285259414045188, 371285255063433865, 371285251777267532, 371285248491242096, 371285246694803527, 371285240779602892, 371285234184178244]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 16590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 16500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 16500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk165
