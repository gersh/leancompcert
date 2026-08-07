import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk271

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471716371047777, 362471726460734560⟩, ⟨366744699871443662, 366929544043951032⟩, true⟩

def state01 : KState := ⟨⟨362516342032471450, 362516352129869366⟩, ⟨(-842757502327603776), (-842572449144247558)⟩, true⟩

def words00 : List Nat := [371285266341492458, 371285266342441059, 371285267437398197, 371285268666103705, 371285269767318863, 371285269768180235, 371285269704443896, 371285270353715765, 371285272363240453, 371285273510521344]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 27100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 27100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362515311893269756, 362515321998535505⟩, ⟨(-814870361132464120), (-814685094612332776)⟩, true⟩

def words01 : List Nat := [371285274387500790, 371285275264701804, 371285277115045373, 371285278288718007, 371285279192070399, 371285280095671118, 371285280878704059, 371285280879584741, 371285281986594321, 371285283095301394]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 27110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 27100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362503228129172666, 362503238242105853⟩, ⟨(-487058834573065812), (-486873360071619962)⟩, true⟩

def words02 : List Nat := [371285285247060882, 371285285806323543, 371285286362181614, 371285286918280828, 371285287554308066, 371285287722908276, 371285289249905897, 371285290777147922, 371285292300923663, 371285292963270882]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 27120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 27100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362516737525551922, 362516747646285002⟩, ⟨(-853572996663386097), (-853387310512315657)⟩, true⟩

def words03 : List Nat := [371285294514295994, 371285296065662278, 371285298723624799, 371285299572556609, 371285300146916586, 371285300721507445, 371285301994401949, 371285302591095871, 371285303750315670, 371285304909815738]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 27130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 27100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362502729281132261, 362502739409650079⟩, ⟨(-473389823956067050), (-473203926488853494)⟩, true⟩

def words04 : List Nat := [371285306079521940, 371285306080384989, 371285306646745655, 371285307609141056, 371285308818512974, 371285308944761682, 371285309067623883, 371285309190765796, 371285310166437595, 371285310809359525]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 27140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 27100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362458476174707040, 362458486311010222⟩, ⟨728452234961181410, 728638343840738390⟩, true⟩

def words05 : List Nat := [371285312424986309, 371285314040853906, 371285315383263630, 371285315384126534, 371285314920059436, 371285314863697950, 371285315638516718, 371285315639380278, 371285314924613868, 371285313937808482]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 27150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 27100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362499554608784745, 362499564752817161⟩, ⟨(-387404411318460961), (-387218092473662365)⟩, true⟩

def words06 : List Nat := [371285313145602190, 371285313146562658, 371285313168704716, 371285313662078871, 371285313947075201, 371285313947941111, 371285313027222754, 371285312670051513, 371285313073866887, 371285313599290473]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 27160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 27100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362517857949218266, 362517868101104717⟩, ⟨(-884774393542543128), (-884587861263323362)⟩, true⟩

def words07 : List Nat := [371285314126671775, 371285314654291176, 371285316167983864, 371285317193722801, 371285318634473445, 371285320075455300, 371285321513414326, 371285321514278293, 371285322556943130, 371285323755375593]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 27170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 27100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362468955398748534, 362468965558342437⟩, ⟨444573852676271759, 444760594484262035⟩, true⟩

def words08 : List Nat := [371285325076379455, 371285325077243451, 371285324595875575, 371285323933981778, 371285323271795661, 371285323016167969, 371285322504167896, 371285322806441428, 371285323063681339, 371285323064575768]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 27180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 27100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362524739387401123, 362524749554819190⟩, ⟨(-1072449110354447517), (-1072262155769224113)⟩, true⟩

def words09 : List Nat := [371285323213548978, 371285323964505831, 371285325865888228, 371285325966834024, 371285325967515299, 371285325644479695, 371285326348035511, 371285326701090080, 371285328151046886, 371285329601296554]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 27190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 27100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 27100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk271
