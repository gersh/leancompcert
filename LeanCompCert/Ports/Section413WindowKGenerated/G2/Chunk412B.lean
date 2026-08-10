import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk412A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk412B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk412A

def state06 : KState := ⟨⟨360568151078668588, 360568161591257879⟩, ⟨585643383304406336, 585936528761342284⟩, true⟩

def words05 : List Nat := [360582363286301530, 360582363919823584, 360582364259297430, 360582364259857971, 360582364014615024, 360582363461324569, 360582362940171793, 360582363013593726, 360582363014094637, 360582362670481373]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360612189728781552, 360612200246661586⟩, ⟨(-1231653726009674843), (-1231360362230827047)⟩, true⟩

def words06 : List Nat := [360582362326761451, 360582361984779806, 360582362615446084, 360582363246188982, 360582363312282774, 360582363312843614, 360582362997491455, 360582362987325326, 360582363552060694, 360582364275586720]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579455469230081, 360579465992457081⟩, ⟨119551959492431568, 119845543967326346⟩, true⟩

def words07 : List Nat := [360582364705194841, 360582365134856744, 360582366011194730, 360582367185285414, 360582368005951189, 360582368826667262, 360582369353670614, 360582369354231399, 360582369297226291, 360582369227533809]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360559092190121379, 360559102718629499⟩, ⟨960239152727219297, 960532955233834117⟩, true⟩

def words08 : List Nat := [360582369672776316, 360582369673337134, 360582369605049569, 360582369088187997, 360582368571260849, 360582367733142567, 360582367352612807, 360582366935495740, 360582366518335213, 360582365807881954]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360595527347769849, 360595537881580388⟩, ⟨(-544470163717759463), (-544176142248547885)⟩, true⟩

def words09 : List Nat := [360582365244942016, 360582365129202742, 360582365013307503, 360582364624580776, 360582364149855006, 360582363178813099, 360582362207710559, 360582361649655616, 360582361703210466, 360582362022830030]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk412B
