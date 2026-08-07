import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk163

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360551217450711317, 360551218964431134⟩, ⟨510372522503107481, 510389226785010863⟩, true⟩

def state01 : KState := ⟨⟨360659730985051636, 360659732500713361⟩, ⟨(-1258989587622846303), (-1258972851678507593)⟩, true⟩

def words00 : List Nat := [360582531100864789, 360582536139364586, 360582539398098134, 360582542656467845, 360582542733252165, 360582542733457700, 360582540787247036, 360582540505195020, 360582542258211678, 360582546990831778]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 16300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 16300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607905121195582, 360607906638812617⟩, ⟨(-413567454068114289), (-413550686222679793)⟩, true⟩

def words01 : List Nat := [360582549822300260, 360582552653444012, 360582555992858990, 360582561203268830, 360582564260820425, 360582567318029918, 360582567318217994, 360582567164335328, 360582566523000718, 360582568075843272]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 16310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 16300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594895042302496, 360594896561855882⟩, ⟨(-201479229654591746), (-201462430198188796)⟩, true⟩

def words02 : List Nat := [360582571182008455, 360582571182214061, 360582570572865140, 360582568067284838, 360582565561973419, 360582562083665856, 360582560859714642, 360582561181201449, 360582561181384708, 360582560365040122]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 16320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 16300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360645184408057240, 360645185929554193⟩, ⟨(-1023297726917531990), (-1023280895713077774)⟩, true⟩

def words03 : List Nat := [360582560984176146, 360582561603293377, 360582565961173846, 360582566607225437, 360582566607418153, 360582563565003620, 360582560522922931, 360582557806540551, 360582561639517552, 360582565472072211]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 16330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 16300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614063079389938, 360614064602845195⟩, ⟨(-515308668684375895), (-515291805471372575)⟩, true⟩

def words04 : List Nat := [360582566884122094, 360582566884327899, 360582564623633872, 360582564660522787, 360582564660698062, 360582562174552789, 360582559185152110, 360582554306877537, 360582549429160471, 360582550211953423]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 16340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 16300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360518693978381954, 360518695503779786⟩, ⟨1044952503996452559, 1044969398980111225⟩, true⟩

def words05 : List Nat := [360582554820431443, 360582559428388548, 360582561533277403, 360582565116647906, 360582567718596457, 360582570320281306, 360582573433227762, 360582573433433764, 360582572843194957, 360582568938925270]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 16350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 16300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360722861539289142, 360722863066632001⟩, ⟨(-2296140043631826180), (-2296123116817731110)⟩, true⟩

def words06 : List Nat := [360582565035086556, 360582566800741840, 360582572469171585, 360582578136947847, 360582580649792917, 360582583519743159, 360582587432185545, 360582591344210716, 360582598978647329, 360582607546699332]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 16360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 16300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360634679319003160, 360634680848315027⟩, ⟨(-852192480663697637), (-852175521607538155)⟩, true⟩

def words07 : List Nat := [360582613445063586, 360582619342727669, 360582625105945893, 360582632729883075, 360582639117574657, 360582645504519802, 360582649641520498, 360582652303939644, 360582655480453559, 360582658656653497]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 16370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 16300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360609506502306331, 360609508033559847⟩, ⟨(-439866774814287901), (-439849783943875161)⟩, true⟩

def words08 : List Nat := [360582665549861423, 360582668751676297, 360582669653199448, 360582670554634986, 360582670554808002, 360582670774806624, 360582671681549884, 360582672588219524, 360582672588405334, 360582673198348825]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 16380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 16300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360668782917229547, 360668784450430925⟩, ⟨(-1411739720191880489), (-1411722697386160939)⟩, true⟩

def words09 : List Nat := [360582676869602096, 360582680540467433, 360582684674325157, 360582688953286632, 360582690098121197, 360582691242832359, 360582693940925467, 360582698548629355, 360582703797937294, 360582709046651512]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 16390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 16300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 16300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk163
