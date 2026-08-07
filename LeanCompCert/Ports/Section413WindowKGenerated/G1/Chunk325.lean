import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk325

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362467102285980379, 362467117020111899⟩, ⟨574005269767523020, 574328928223445850⟩, true⟩

def state01 : KState := ⟨⟨362469693571472494, 362469708314996979⟩, ⟨489869973264963196, 490193937039610058⟩, true⟩

def words00 : List Nat := [371284788136439294, 371284787986783932, 371284787684354327, 371284788005969349, 371284788083518593, 371284788084566922, 371284786902148986, 371284786664196436, 371284786564820628, 371284786565905611]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 32500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 32500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362456604361715081, 362456619114793108⟩, ⟨915481222527908496, 915805496937006168⟩, true⟩

def words01 : List Nat := [371284786102900801, 371284785641960661, 371284785180612549, 371284785090250450, 371284784526917086, 371284783997191764, 371284783467155272, 371284782934124878, 371284781280125209, 371284780415436928]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 32510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 32500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362441387472774475, 362441402235214778⟩, ⟨1410524308207801317, 1410848887126322547⟩, true⟩

def words02 : List Nat := [371284779550209098, 371284779283680604, 371284778392058975, 371284777429082135, 371284776465773814, 371284775784088344, 371284774750328557, 371284774208328133, 371284773666005473, 371284772935710515]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 32520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 32500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500459632039622, 362500474403950800⟩, ⟨(-511366530778216666), (-511041643723887582)⟩, true⟩

def words03 : List Nat := [371284771603211664, 371284771213937746, 371284771376242908, 371284771377292192, 371284770672345733, 371284769811083469, 371284769029437455, 371284769030605135, 371284769373780368, 371284769857571652]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 32530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 32500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362447590321650558, 362447605103047046⟩, ⟨1209199249796542564, 1209524445550105340⟩, true⟩

def words04 : List Nat := [371284770342006695, 371284770343056670, 371284769726732272, 371284769502679722, 371284769278097934, 371284769183884227, 371284767832551444, 371284766430131998, 371284765027386992, 371284764072188371]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 32540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 32500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362416684758080787, 362416699548934621⟩, ⟨2215477303931581726, 2215802807570245012⟩, true⟩

def words05 : List Nat := [371284762931340145, 371284762565642254, 371284762199606115, 371284761832048154, 371284760384666597, 371284759006059245, 371284757627018028, 371284756640066636, 371284754549654758, 371284752460715034]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 32550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 32500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362463075843470108, 362463090643720144⟩, ⟨704853779114009588, 705179588740772760⟩, true⟩

def words06 : List Nat := [371284750371415307, 371284749223644231, 371284747645634780, 371284747009045448, 371284746372162988, 371284745630706947, 371284743915861346, 371284742911863774, 371284741907374158, 371284741843865701]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 32560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 32500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491804033538165, 362491818843373695⟩, ⟨(-231032617427988453), (-230706495553759319)⟩, true⟩

def words07 : List Nat := [371284741179939774, 371284740190010417, 371284739199722106, 371284739150343374, 371284738679985052, 371284738491783219, 371284738303224372, 371284738116026055, 371284737611393296, 371284737830036052]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 32570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 32500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482675463259559, 362482690282443539⟩, ⟨66511022026857417, 66837448523408813⟩, true⟩

def words08 : List Nat := [371284738835288409, 371284738997032768, 371284739159724985, 371284739322770357, 371284739525379419, 371284739526537115, 371284739929693330, 371284740601799759, 371284741138935380, 371284741140023270]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 32580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 32500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490527539073339, 362490542367787346⟩, ⟨(-189431796858361428), (-189105059731502614)⟩, true⟩

def words09 : List Nat := [371284741411310617, 371284741746079044, 371284742568544454, 371284742569596226, 371284742307294085, 371284741841673324, 371284741631281517, 371284741632450426, 371284741597892481, 371284741777016158]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 32590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 32500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 32500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk325
