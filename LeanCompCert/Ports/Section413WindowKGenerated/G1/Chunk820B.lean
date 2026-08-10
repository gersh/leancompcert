import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk820A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk820B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk820A

def state06 : KState := ⟨⟨362489501501660703, 362489602673878920⟩, ⟨(-364106991614832768), (-358501027109400966)⟩, true⟩

def words05 : List Nat := [371285232760225245, 371285232969778680, 371285233177089124, 371285233261962858, 371285233391456062, 371285233522393894, 371285233774933155, 371285233848234694, 371285233903604480, 371285233960030571]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494700807885125, 362494802005570993⟩, ⟨(-790775819610560577), (-785167765099418951)⟩, true⟩

def words06 : List Nat := [371285234055128719, 371285234089527327, 371285234253706094, 371285234419079848, 371285234559349151, 371285234562193142, 371285234645847417, 371285234764394129, 371285234952971497, 371285235072487451]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493256180143210, 362493357403769051⟩, ⟨(-672197082804777597), (-666586899276693835)⟩, true⟩

def words07 : List Nat := [371285235162230596, 371285235252922595, 371285235490925224, 371285235656013901, 371285235820312106, 371285235985640401, 371285236148331107, 371285236151174056, 371285236214739158, 371285236317290126]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494274201478978, 362494375450448748⟩, ⟨(-755689927400936103), (-750077663510822243)⟩, true⟩

def words08 : List Nat := [371285236552356395, 371285236739614979, 371285236925976994, 371285237113269093, 371285237344987116, 371285237503739966, 371285237740993469, 371285237979422759, 371285238187625527, 371285238301875691]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362500755160228887, 362500856434879085⟩, ⟨(-1287738912959932357), (-1282124540831428741)⟩, true⟩

def words09 : List Nat := [371285238545674403, 371285238790910909, 371285239072219251, 371285239156633070, 371285239226946053, 371285239298224191, 371285239494970036, 371285239619082388, 371285239811234080, 371285240004618414]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk820B
