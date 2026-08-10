import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk377A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360646013825314421, 360646022537832246⟩, ⟨(-2429161456507029653), (-2428939429785238409)⟩, true⟩

def state01 : KState := ⟨⟨360637291880229423, 360637300597596087⟩, ⟨(-2100414829260021930), (-2100192619712729574)⟩, true⟩

def words00 : List Nat := [360581597385063056, 360581598646104422, 360581600305320577, 360581601964597382, 360581603443859549, 360581604689184423, 360581605581114991, 360581606473057198, 360581607342709627, 360581608820138244]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584054128559614, 360584062850714197⟩, ⟨(-92433081567431415), (-92210691443807369)⟩, true⟩

def words01 : List Nat := [360581610733840018, 360581612647537478, 360581614109494016, 360581615050497010, 360581615655296080, 360581616260206360, 360581617567391074, 360581618174855526, 360581618240127400, 360581618305462380]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360627865596619973, 360627874323583231⟩, ⟨(-1745332955381347333), (-1745110383850844885)⟩, true⟩

def words02 : List Nat := [360581618847600592, 360581619741823571, 360581620332833232, 360581620923900691, 360581620924370199, 360581620918314994, 360581620929186806, 360581621142066906, 360581621728719809, 360581622955110335]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603694099157809, 360603702830960335⟩, ⟨(-833131115278523381), (-832908361138367705)⟩, true⟩

def words03 : List Nat := [360581623828595910, 360581624702090768, 360581626071419235, 360581627883036928, 360581629515189212, 360581631147338154, 360581632223809982, 360581632601259053, 360581633186469196, 360581633771816742]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591284794616337, 360591293531207730⟩, ⟨(-364908841767489659), (-364685906871632691)⟩, true⟩

def words04 : List Nat := [360581634240959104, 360581634241468046, 360581634195260292, 360581633687559692, 360581633179794282, 360581632493222395, 360581632560328714, 360581632944776442, 360581632976855923, 360581633233285248]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk377A
