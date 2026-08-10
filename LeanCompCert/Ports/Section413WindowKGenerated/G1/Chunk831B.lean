import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk831A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk831B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk831A

def state06 : KState := ⟨⟨362486706764232473, 362486810773885635⟩, ⟨(-130061294122077922), (-124220925085359684)⟩, true⟩

def words05 : List Nat := [371285316629634211, 371285316684524916, 371285316798950075, 371285316842427747, 371285316928912590, 371285317016473750, 371285317100314039, 371285317103197214, 371285317012043628, 371285317033729969]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475563762665693, 362475667797969251⟩, ⟨796667871686212965, 802510373944376907⟩, true⟩

def words06 : List Nat := [371285317149941347, 371285317152825743, 371285317100801149, 371285317044509504, 371285316987132360, 371285316975079419, 371285316897643421, 371285316877010705, 371285316855379616, 371285316834568318]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499610819750682, 362499714881076892⟩, ⟨(-1203458795712714999), (-1197614129016708633)⟩, true⟩

def words07 : List Nat := [371285316720523000, 371285316681955486, 371285316720210318, 371285316723158480, 371285316719621618, 371285316696844932, 371285316791508498, 371285316841199427, 371285317016250325, 371285317192554072]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492245398562624, 362492349485953149⟩, ⟨(-590794204322173034), (-584947369464392050)⟩, true⟩

def words08 : List Nat := [371285317320620698, 371285317352526161, 371285317518630252, 371285317686265403, 371285317884977144, 371285317891929534, 371285317897863999, 371285317904766997, 371285318020111416, 371285318107925906]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481803841776690, 362481907955163502⟩, ⟨277917553227743603, 283766550846933099⟩, true⟩

def words09 : List Nat := [371285318297656630, 371285318488579935, 371285318650721434, 371285318653606201, 371285318623060004, 371285318601042951, 371285318684213478, 371285318687106272, 371285318648512823, 371285318610822720]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk831B
