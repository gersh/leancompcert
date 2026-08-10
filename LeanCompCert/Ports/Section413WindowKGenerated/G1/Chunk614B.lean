import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk614A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk614B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk614A

def state06 : KState := ⟨⟨362480978505831498, 362481033994990352⟩, ⟨262764923235693291, 265068500000662473⟩, true⟩

def words05 : List Nat := [371285347608215325, 371285347706611112, 371285347912986219, 371285347915069737, 371285347768700563, 371285347550470589, 371285347331380156, 371285347194540991, 371285346924827934, 371285346857014444]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 61450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 61400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471702200534404, 362471757708493541⟩, ⟨832886138175859569, 835190870502503193⟩, true⟩

def words06 : List Nat := [371285346788414414, 371285346720913300, 371285346334172449, 371285346213412992, 371285346091600380, 371285346035270726, 371285345665903534, 371285345247758430, 371285344828782924, 371285344675640158]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 61460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 61400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467416032119052, 362467471558861512⟩, ⟨1096482504408067945, 1098788391439321389⟩, true⟩

def words07 : List Nat := [371285344499825154, 371285344545922509, 371285344600319324, 371285344602439822, 371285344437476643, 371285344355185092, 371285344361593063, 371285344363677850, 371285344137240713, 371285343848897936]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 61470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 61400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483591495190073, 362483647040634206⟩, ⟨101930408597002350, 104237445498780806⟩, true⟩

def words08 : List Nat := [371285343559640421, 371285343380130558, 371285343067899184, 371285343021247894, 371285342973963319, 371285342887365234, 371285342483332680, 371285342345210923, 371285342231904701, 371285342234088407]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 61480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 61400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487847915993832, 362487903480361180⟩, ⟨(-159791625093050105), (-157483424505749551)⟩, true⟩

def words09 : List Nat := [371285342208078952, 371285342186113917, 371285342403793792, 371285342527400493, 371285342657559277, 371285342788504747, 371285342919513945, 371285342921599360, 371285342771708680, 371285342815908476]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 61490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 61400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 61400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk614B
