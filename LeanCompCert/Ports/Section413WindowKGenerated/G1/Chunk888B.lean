import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk888A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk888B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk888A

def state06 : KState := ⟨⟨362487682328701516, 362487801693833399⟩, ⟨(-242733462289775278), (-235571845376025208)⟩, true⟩

def words05 : List Nat := [371285150675191806, 371285150607604621, 371285150594368718, 371285150597782557, 371285150615218859, 371285150637416036, 371285150660341787, 371285150663514485, 371285150645180510, 371285150678816958]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481507073502008, 362481626466203543⟩, ⟨306058504284058893, 313222571184122639⟩, true⟩

def words06 : List Nat := [371285150837227102, 371285150840846429, 371285150843166477, 371285150843138429, 371285150844249919, 371285150847695726, 371285150853837050, 371285150922440829, 371285150965879264, 371285150969086227]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362494500834003287, 362494620254778846⟩, ⟨(-848728133382866802), (-841561571408326026)⟩, true⟩

def words07 : List Nat := [371285151010563565, 371285151093403017, 371285151300990625, 371285151362437282, 371285151406495590, 371285151451473220, 371285151570700395, 371285151628032015, 371285151736702051, 371285151846779293]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493592204089216, 362493711652784411⟩, ⟨(-767997126254787408), (-760828082639342888)⟩, true⟩

def words08 : List Nat := [371285151951859519, 371285151954964349, 371285152026709679, 371285152128458958, 371285152251515836, 371285152271058596, 371285152289717537, 371285152309452064, 371285152440309966, 371285152540133644]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483703390470344, 362483822867080403⟩, ⟨111096033649061559, 118267558755346945⟩, true⟩

def words09 : List Nat := [371285152703317491, 371285152867717459, 371285153000192983, 371285153015580409, 371285153045019198, 371285153076033665, 371285153231785612, 371285153234884147, 371285153222271285, 371285153210823433]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk888B
