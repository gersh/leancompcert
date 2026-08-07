import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk807

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490492550478455, 362490590271537885⟩, ⟨(-443892379451446518), (-438567277670332158)⟩, true⟩

def state01 : KState := ⟨⟨362477695844950536, 362477793590905592⟩, ⟨588886890949198268, 594214001935848842⟩, true⟩

def words00 : List Nat := [371285156022794680, 371285156041783346, 371285156043929609, 371285156027922353, 371285156039030550, 371285156042107073, 371285155995450622, 371285155972329504, 371285155948291402, 371285155925212814]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 80700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 80700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490989871677758, 362491087642895337⟩, ⟨(-484128369981246155), (-478799219930133821)⟩, true⟩

def words01 : List Nat := [371285155871895439, 371285155911307156, 371285156102590313, 371285156105382333, 371285156092416521, 371285156054848497, 371285156016204479, 371285156016095633, 371285156033923349, 371285156110581192]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 80710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 80700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474548419734632, 362474646216162035⟩, ⟨843090571387748325, 848421756501969243⟩, true⟩

def words02 : List Nat := [371285156185794037, 371285156188586392, 371285156062172466, 371285156068603979, 371285156118707038, 371285156121499550, 371285155981846776, 371285155836016103, 371285155689041343, 371285155590081297]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 80720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 80700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468495951478822, 362468593773054307⟩, ⟨1331730933090940541, 1337064148538231535⟩, true⟩

def words03 : List Nat := [371285155461834924, 371285155374239988, 371285155285735217, 371285155179409117, 371285154894848808, 371285154645622584, 371285154394910517, 371285154298461302, 371285154095768371, 371285153893794191]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 80730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 80700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484646014778369, 362484743861321065⟩, ⟨27697796516798651, 33033027945804003⟩, true⟩

def words04 : List Nat := [371285153690586726, 371285153627877115, 371285153487284334, 371285153449392318, 371285153410644433, 371285153335244254, 371285153082310997, 371285152984100225, 371285152936157058, 371285152939066524]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 80740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 80700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477876872675949, 362477974744723223⟩, ⟨574368292618873072, 579705583671251812⟩, true⟩

def words05 : List Nat := [371285152936102893, 371285152905466604, 371285152948624609, 371285152958043686, 371285153005166772, 371285153053346383, 371285153098999702, 371285153101793464, 371285152957703681, 371285152872307068]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 80750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 80700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477819279441080, 362477917176386870⟩, ⟨579056245946954957, 584395547932391715⟩, true⟩

def words06 : List Nat := [371285152849669423, 371285152852482193, 371285152781567266, 371285152711631024, 371285152640652846, 371285152595260068, 371285152493341753, 371285152489376270, 371285152484441804, 371285152480929800]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 80760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 80700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362486998709282334, 362487096631459819⟩, ⟨(-162451999555223513), (-157110659476081431)⟩, true⟩

def words07 : List Nat := [371285152401077782, 371285152412221543, 371285152440094558, 371285152442888921, 371285152266783283, 371285152064224654, 371285151860504397, 371285151811139009, 371285151708021546, 371285151735265466]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 80770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 80700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483565428347529, 362483663375749895⟩, ⟨114878427232087854, 120221805098999394⟩, true⟩

def words08 : List Nat := [371285151761492924, 371285151764300995, 371285151681575277, 371285151719289813, 371285151790223058, 371285151793019916, 371285151691781790, 371285151561635053, 371285151450357118, 371285151453545402]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 80700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481362667838864, 362481460640421499⟩, ⟨292913718727922380, 298259131037044648⟩, true⟩

def words09 : List Nat := [371285151561271405, 371285151688575703, 371285151810833065, 371285151834344173, 371285151859596859, 371285151886178137, 371285152038500241, 371285152041295950, 371285152008800656, 371285151966300671]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 80790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 80700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 80700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk807
