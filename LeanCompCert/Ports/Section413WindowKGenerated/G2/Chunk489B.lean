import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk489A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk489B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk489A

def state06 : KState := ⟨⟨360582659056513209, 360582674068613137⟩, ⟨(-33378600839032130), (-32881948990141632)⟩, true⟩

def words05 : List Nat := [360582006269156356, 360582005402722992, 360582004536195317, 360582004085851013, 360582003887082035, 360582003584601867, 360582003282060399, 360582002771772962, 360582002459399679, 360582002473895094]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360557612882197619, 360557627900641772⟩, ⟨1192897140352851013, 1193394102847995725⟩, true⟩

def words06 : List Nat := [360582002552175807, 360582002552850405, 360582002214231286, 360582001620192512, 360582001026077721, 360582000138364435, 360581999461648800, 360581998978891918, 360581998496086640, 360581997802680735]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561532866646157, 360561547891470295⟩, ⟨1000942067816826236, 1001439342770484638⟩, true⟩

def words07 : List Nat := [360581997305589387, 360581996932861185, 360581996602033662, 360581996602708656, 360581996375880562, 360581995799293490, 360581995222602516, 360581994599550862, 360581994191078914, 360581993774336169]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360556773404572968, 360556788435822094⟩, ⟨1233838921112356751, 1234336510793017283⟩, true⟩

def words08 : List Nat := [360581993357513062, 360581992675670544, 360581991817642552, 360581990887887579, 360581989957988509, 360581988821877203, 360581987699937247, 360581986367744158, 360581985035475868, 360581984118834812]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360533885864642827, 360533900902258947⟩, ⟨2355360358520483319, 2355858260152055283⟩, true⟩

def words09 : List Nat := [360581983605088514, 360581983506823437, 360581983408498986, 360581982985681569, 360581982713940969, 360581982233243531, 360581981752363553, 360581981395739449, 360581980622768901, 360581979642262051]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk489B
