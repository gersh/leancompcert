import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk941A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360616615269647464, 360616673676079173⟩, ⟨(-3259792566513886572), (-3256081313794381350)⟩, true⟩

def state01 : KState := ⟨⟨360600995969465449, 360601054388890020⟩, ⟨(-1790050863032463437), (-1786338387619952287)⟩, true⟩

def words00 : List Nat := [360582071973861012, 360582072143407571, 360582072406169178, 360582072669339664, 360582072831045745, 360582072906719128, 360582072907941637, 360582072901484509, 360582072999728966, 360582073202975303]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582252875556561, 360582311307810740⟩, ⟨(-25989144167874160), (-22275461297316876)⟩, true⟩

def words01 : List Nat := [360582073518591752, 360582073834466616, 360582074093865193, 360582074240879373, 360582074310207858, 360582074379890115, 360582074561974368, 360582074631804543, 360582074635533377, 360582074639465766]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591118495913269, 360591176941052061⟩, ⟨(-860371777244311461), (-856656881613686011)⟩, true⟩

def words02 : List Nat := [360582074755893955, 360582074958930072, 360582075241239722, 360582075523804573, 360582075708556049, 360582075843526094, 360582075964214665, 360582076085294393, 360582076154751739, 360582076252845055]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589825124057409, 360589883582184617⟩, ⟨(-738636463936491708), (-734920345641631786)⟩, true⟩

def words03 : List Nat := [360582076294470875, 360582076336233408, 360582076406019098, 360582076548428109, 360582076648124565, 360582076748065696, 360582076791217792, 360582076821997008, 360582076906027582, 360582076990522731]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590110349423256, 360590168820412076⟩, ⟨(-765528672107318233), (-761811342957701773)⟩, true⟩

def words04 : List Nat := [360582077151189989, 360582077227181347, 360582077228416979, 360582077217564983, 360582077206493162, 360582077164493054, 360582077256265199, 360582077348296048, 360582077354896122, 360582077442275278]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk941A
