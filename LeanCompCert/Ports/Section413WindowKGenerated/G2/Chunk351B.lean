import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk351A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk351B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk351A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk351B
