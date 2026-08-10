import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk749A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk749B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk749A

def state06 : KState := ⟨⟨362516894534040383, 362516978370017154⟩, ⟨(-2382680788347918687), (-2378436888266062241)⟩, true⟩

def words05 : List Nat := [371285246797650831, 371285247045948923, 371285247405906788, 371285247607110594, 371285247789021559, 371285247971751714, 371285248279487128, 371285248527847171, 371285248952886737, 371285249379098329]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 74950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 74900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497202692280513, 362497286551559489⟩, ⟨(-906533658786061282), (-902288011853129540)⟩, true⟩

def words06 : List Nat := [371285249803595588, 371285250023347870, 371285250316606583, 371285250611136255, 371285250893427808, 371285250939381156, 371285250984875711, 371285251031263476, 371285251227575530, 371285251391139419]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 74960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 74900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481411735774184, 362481495618248465⟩, ⟨277446402880450506, 281693788882790756⟩, true⟩

def words07 : List Nat := [371285251651324279, 371285251912520098, 371285252156215526, 371285252216134955, 371285252329319636, 371285252443834388, 371285252631301898, 371285252633881756, 371285252584506622, 371285252537278644]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 74970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 74900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479163858200588, 362479247763758479⟩, ⟨446078631066191958, 450327747996653228⟩, true⟩

def words08 : List Nat := [371285252587619864, 371285252600238465, 371285252773359600, 371285252947612381, 371285253092216177, 371285253094796307, 371285253002215671, 371285252951024856, 371285252931750121, 371285252934421190]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 74980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 74900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487390778889238, 362487474708010066⟩, ⟨(-170916265863335587), (-166665381830820115)⟩, true⟩

def words09 : List Nat := [371285252856305034, 371285252743375054, 371285252645335567, 371285252648181576, 371285252595038118, 371285252589884725, 371285252583910699, 371285252576573037, 371285252499694536, 371285252532547995]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 74990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 74900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 74900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk749B
