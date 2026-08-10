import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk351A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk351A
