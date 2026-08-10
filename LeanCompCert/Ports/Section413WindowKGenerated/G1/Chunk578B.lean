import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk578A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk578B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk578A

def state06 : KState := ⟨⟨362506092281864271, 362506141225909407⟩, ⟨(-1226232859512404754), (-1224319892115978184)⟩, true⟩

def words05 : List Nat := [371284980042794226, 371284980162242443, 371284980579767468, 371284980599489867, 371284980601032054, 371284980567512077, 371284980748225414, 371284980817063049, 371284981184105503, 371284981551999244]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 57850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 57800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486625385528185, 362486674347212793⟩, ⟨(-99786252332590463), (-97872264224748403)⟩, true⟩

def words06 : List Nat := [371284981918023763, 371284982037252353, 371284982353157608, 371284982670073649, 371284983050817342, 371284983052770231, 371284983035335728, 371284983017054335, 371284983101415117, 371284983132887402]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 57860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 57800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475219947668897, 362475268926957478⟩, ⟨560355026883187608, 562270033822379046⟩, true⟩

def words07 : List Nat := [371284983315855992, 371284983499628419, 371284983671172137, 371284983673129478, 371284983536236443, 371284983490853595, 371284983644956574, 371284983646910752, 371284983502292700, 371284983336664154]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 57870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 57800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483684349740021, 362483733346549770⟩, ⟨70449039507147436, 72365060657220720⟩, true⟩

def words08 : List Nat := [371284983301135191, 371284983327327602, 371284983475105853, 371284983623634090, 371284983675701944, 371284983677655872, 371284983368963226, 371284983325739588, 371284983388725335, 371284983390782923]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 57880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 57800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475357136850290, 362475406151408827⟩, ⟨552556986569815468, 554474035289900802⟩, true⟩

def words09 : List Nat := [371284983370653004, 371284983329378630, 371284983342353939, 371284983344507098, 371284983252704328, 371284983251472923, 371284983249604657, 371284983185323983, 371284982722615738, 371284982559617634]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 57890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 57800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 57800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk578B
