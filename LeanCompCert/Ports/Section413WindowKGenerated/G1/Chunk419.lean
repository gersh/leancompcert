import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk419

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362505994715526431, 362506019721538085⟩, ⟨(-875937274649497062), (-875229312482748816)⟩, true⟩

def state01 : KState := ⟨⟨362492705235586887, 362492730254056481⟩, ⟨(-319036193286768852), (-318327709070122272)⟩, true⟩

def words00 : List Nat := [371285132191113308, 371285132309913018, 371285132997608913, 371285133686020716, 371285134373983313, 371285134451122765, 371285134470395982, 371285134490120833, 371285134745218256, 371285134928030614]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 41900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 41900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484958572276193, 362484983603171481⟩, ⟨5794302006998963, 6503307047254163⟩, true⟩

def words01 : List Nat := [371285135679390623, 371285136431295637, 371285137182789597, 371285137349560365, 371285137637347795, 371285137925815230, 371285138711937812, 371285138740412678, 371285138741444268, 371285138739312876]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 41910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 41900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487685715335716, 362487710758594147⟩, ⟨(-108560450545990198), (-107850927179529014)⟩, true⟩

def words02 : List Nat := [371285138896470214, 371285138898008278, 371285138950281898, 371285139072582665, 371285139160071185, 371285139161451040, 371285138490988302, 371285138390122549, 371285138590979026, 371285138653774813]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 41920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 41900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490116383093415, 362490141438918874⟩, ⟨(-210449129145655731), (-209739078779114525)⟩, true⟩

def words03 : List Nat := [371285138714521882, 371285138775718472, 371285139248976951, 371285139493954977, 371285139909158823, 371285140324888629, 371285140625219412, 371285140626606317, 371285140505431978, 371285140626377945]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 41930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 41900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482915503077146, 362482940571183152⟩, ⟨91638727890615038, 92349293367615754⟩, true⟩

def words04 : List Nat := [371285141314941469, 371285141333995153, 371285141335035518, 371285141230362967, 371285141189743327, 371285141191264109, 371285141321940301, 371285141672409202, 371285141983181935, 371285141984612655]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 41940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 41900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362527093189325378, 362527118269953436⟩, ⟨(-1761903783543872085), (-1761192692705941685)⟩, true⟩

def words05 : List Nat := [371285142024122659, 371285142116823275, 371285142776916870, 371285142928973951, 371285142996357412, 371285143064158684, 371285143699493768, 371285144133352995, 371285145134627091, 371285146136479355]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 41950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 41900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495985932024596, 362496011025095778⟩, ⟨(-456581243079237628), (-455869630063268886)⟩, true⟩

def words06 : List Nat := [371285147138578988, 371285147384403820, 371285148046229310, 371285148708729518, 371285149303492978, 371285149304874224, 371285149143256111, 371285148982370345, 371285149226283360, 371285149486651060]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 41960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 41900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362465333470225933, 362465358575744949⟩, ⟨830156635304172154, 830868770817844780⟩, true⟩

def words07 : List Nat := [371285150100122644, 371285150714137069, 371285151252801337, 371285151254183940, 371285151157323275, 371285151120669656, 371285151415414767, 371285151416796483, 371285151060230779, 371285150590295160]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 41970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 41900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362505173372261838, 362505198490147908⟩, ⟨(-842476902990429364), (-841764248244956126)⟩, true⟩

def words08 : List Nat := [371285150215848641, 371285150217370674, 371285150411664925, 371285150793590492, 371285151087011828, 371285151088417556, 371285150999682246, 371285151090078071, 371285151709750454, 371285152188601269]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 41980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 41900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362514110871702871, 362514136002212952⟩, ⟨(-1217848814815091219), (-1217135629926125649)⟩, true⟩

def words09 : List Nat := [371285152665639924, 371285153143135594, 371285153849819541, 371285154274742176, 371285154771881218, 371285155269512219, 371285155765392833, 371285155889750047, 371285156580690921, 371285157272422564]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 41990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 41900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 41900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk419
