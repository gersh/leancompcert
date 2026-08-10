import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk719A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk719B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk719A

def state06 : KState := ⟨⟨362484218938439698, 362484295953008921⟩, ⟨65101300008757812, 68844024504631270⟩, true⟩

def words05 : List Nat := [371285253713131919, 371285253691478192, 371285253692943492, 371285253695412105, 371285253464431842, 371285253204124387, 371285252942842678, 371285252844938665, 371285252661965462, 371285252651515100]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473710452550705, 362473787489389500⟩, ⟨821320923048714553, 825065250177992591⟩, true⟩

def words06 : List Nat := [371285252640071310, 371285252609585223, 371285252405274192, 371285252395174931, 371285252405721528, 371285252408190515, 371285252174704977, 371285251894428591, 371285251613107796, 371285251505648747]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481527766355979, 362481604825387743⟩, ⟨258714429895282071, 262460354367031313⟩, true⟩

def words07 : List Nat := [371285251381633109, 371285251417891169, 371285251419767210, 371285251418788376, 371285251279743788, 371285251202258950, 371285251215612630, 371285251218091430, 371285251168852777, 371285251120947163]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492227188520915, 362492304269697058⟩, ⟨(-511485637791627009), (-507738119255303029)⟩, true⟩

def words08 : List Nat := [371285251072004109, 371285251072956827, 371285251106857265, 371285251222100623, 371285251305361421, 371285251307831234, 371285251150820955, 371285251170853419, 371285251369244398, 371285251469774078]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491641801228576, 362491718904950029⟩, ⟨(-469320132961333221), (-465570991282018487)⟩, true⟩

def words09 : List Nat := [371285251562648107, 371285251656354262, 371285251941783131, 371285252159166984, 371285252324684255, 371285252491074674, 371285252647013998, 371285252649484206, 371285252638051848, 371285252730990195]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk719B
