import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk719

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497766966310454, 362497843847440645⟩, ⟨(-908860618909258345), (-905127492688314265)⟩, true⟩

def state01 : KState := ⟨⟨362484140647607460, 362484217551023170⟩, ⟨70878825629232040, 74613554288875838⟩, true⟩

def words00 : List Nat := [371285255498320831, 371285255500787702, 371285255461841752, 371285255508517378, 371285255610825306, 371285255613292381, 371285255476796579, 371285255302847541, 371285255144534816, 371285255147383744]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 71900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 71900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482304960086126, 362482381885766512⟩, ⟨202896720161582831, 206633049985177665⟩, true⟩

def words01 : List Nat := [371285255201209930, 371285255270460048, 371285255339220606, 371285255341688840, 371285255184980731, 371285255074114074, 371285255041353131, 371285255043880601, 371285255018706328, 371285254981567196]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 71910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 71900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476100299096500, 362476177246849647⟩, ⟨649224236476585015, 652962153885444253⟩, true⟩

def words02 : List Nat := [371285254997286264, 371285255000005398, 371285255083446320, 371285255210669286, 371285255286941950, 371285255289409635, 371285255107905746, 371285255050582017, 371285254991945936, 371285254991238434]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 71920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 71900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474121398404008, 362474198368636127⟩, ⟨791638204430987564, 795377738865798470⟩, true⟩

def words03 : List Nat := [371285254866882661, 371285254743766253, 371285254686894486, 371285254689619850, 371285254737851627, 371285254793034944, 371285254846949038, 371285254849417091, 371285254645752214, 371285254495114662]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 71930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 71900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477755556354891, 362477832548561303⟩, ⟨530218975249874693, 533960090629532533⟩, true⟩

def words04 : List Nat := [371285254382465334, 371285254384945467, 371285254241304469, 371285254098918352, 371285253955557545, 371285253871709714, 371285253751703265, 371285253790023785, 371285253812029891, 371285253814588121]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 71940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 71900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk719
