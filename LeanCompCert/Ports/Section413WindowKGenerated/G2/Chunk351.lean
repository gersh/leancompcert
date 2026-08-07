import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk351

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360647982334374414, 360647989842553628⟩, ⟨(-2319558326483657552), (-2319380157756559846)⟩, true⟩

def state01 : KState := ⟨⟨360614843518791581, 360614851031397812⟩, ⟨(-1156358462413811411), (-1156180138275641839)⟩, true⟩

def words00 : List Nat := [360581914519165546, 360581915710921981, 360581916493726110, 360581917276537147, 360581917276939039, 360581917665385004, 360581918872818762, 360581920080273968, 360581920807661454, 360581921746037793]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 35100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 35100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360628960509025278, 360628968026083071⟩, ⟨(-1652051246337222299), (-1651872765882749313)⟩, true⟩

def words01 : List Nat := [360581923494103744, 360581925242221491, 360581926873598965, 360581927963804877, 360581928360715361, 360581928757640198, 360581929964141361, 360581931584367140, 360581932924061376, 360581934263778959]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 35110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 35100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360639289842235612, 360639297363778201⟩, ⟨(-2015199512081233453), (-2015020874098198805)⟩, true⟩

def words02 : List Nat := [360581935089518534, 360581935651368663, 360581936052229027, 360581936453201644, 360581936638037649, 360581937179985844, 360581937312197481, 360581937444448854, 360581938385897156, 360581940019151000]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 35120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 35100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360576517942562322, 360576525468549423⟩, ⟨190403982179470749, 190582776320582157⟩, true⟩

def words03 : List Nat := [360581941802268857, 360581943585374476, 360581944724414770, 360581945747445163, 360581946567847095, 360581947388331903, 360581948672787767, 360581949150043570, 360581949150466547, 360581948996617738]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 35130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 35100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360629940688336032, 360629948218768226⟩, ⟨(-1687111291740966285), (-1686932341377293013)⟩, true⟩

def words04 : List Nat := [360581949497010318, 360581950557287408, 360581952245594886, 360581953933897181, 360581954810953620, 360581954881117492, 360581954928961226, 360581954976934172, 360581955833033114, 360581957198843408]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 35140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 35100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360638775541618322, 360638783076540567⟩, ⟨(-1997679503970186080), (-1997500395759681722)⟩, true⟩

def words05 : List Nat := [360581958156673718, 360581959114503273, 360581960880280702, 360581963261673164, 360581965284451432, 360581967307196091, 360581968922151711, 360581969730652983, 360581971346886014, 360581972963183164]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 35150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 35100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576050730321593, 360576058269688775⟩, ⟨207954706216131421, 208133970733364005⟩, true⟩

def words06 : List Nat := [360581974557252979, 360581975344993241, 360581975727450970, 360581976109934697, 360581976110331202, 360581976358958399, 360581976473170514, 360581976587471464, 360581976587892570, 360581976210283981]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 35160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 35100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360630289380944151, 360630296924764122⟩, ⟨(-1699966678222576014), (-1699787257079113332)⟩, true⟩

def words07 : List Nat := [360581976681582035, 360581977321248523, 360581978226293342, 360581978647585890, 360581978648028820, 360581978265986993, 360581977925643432, 360581978686960830, 360581980060799996, 360581981434667789]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 35170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 35100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602880636274519, 360602888184597583⟩, ⟨(-735631331494296579), (-735451751910607327)⟩, true⟩

def words08 : List Nat := [360581982400697417, 360581983419153597, 360581985045830651, 360581986672553387, 360581987922131524, 360581988619741557, 360581988797811603, 360581988975923922, 360581988976314820, 360581989325460003]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 35180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 35100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360538074219979604, 360538081772746093⟩, ⟨1545309888410944353, 1545489624381697675⟩, true⟩

def words09 : List Nat := [360581990154849407, 360581990984280410, 360581991406613410, 360581991407085536, 360581991024802536, 360581990440449007, 360581989855981682, 360581989817679087, 360581988974855536, 360581987727984210]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 35190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 35100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 35100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk351
