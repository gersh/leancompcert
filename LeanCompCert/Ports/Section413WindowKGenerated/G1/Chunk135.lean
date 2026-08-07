import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk135

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362533054540365661, 362533056896995239⟩, ⟨(-653556526314465907), (-653535001143870971)⟩, true⟩

def state01 : KState := ⟨⟨362477262316950993, 362477264677191095⟩, ⟨99940274491992253, 99961848423481099⟩, true⟩

def words00 : List Nat := [371284657798565009, 371284658929990903, 371284658989701613, 371284659049540010, 371284660033106277, 371284660033551869, 371284660162608512, 371284662032508437, 371284663777314488, 371284663777740576]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 13500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 13500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362541184498747289, 362541186862651667⟩, ⟨(-763775195800815710), (-763753572346430212)⟩, true⟩

def words01 : List Nat := [371284666830746327, 371284670431066357, 371284679497476720, 371284682734702068, 371284684615448975, 371284686496039196, 371284690620376664, 371284692034458454, 371284696213347312, 371284700391802882]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 13510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 13500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489349924872193, 362489352292432060⟩, ⟨(-62957568759396688), (-62935895864247996)⟩, true⟩

def words02 : List Nat := [371284704566693505, 371284704567098916, 371284703823118248, 371284706179869079, 371284710094957826, 371284710095363276, 371284706738820478, 371284703201425471, 371284700710602266, 371284701054839551]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 13520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 13500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362467448835888437, 362467451207102801⟩, ⟨233540120651745099, 233561843011020377⟩, true⟩

def words03 : List Nat := [371284703645872972, 371284706236680534, 371284708626945283, 371284708627351291, 371284704745354349, 371284702521003148, 371284703517795422, 371284703518208321, 371284702247570635, 371284700973942611]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 13530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 13500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470886523917614, 362470888898765432⟩, ⟨187188367241116152, 187210138816221366⟩, true⟩

def words04 : List Nat := [371284701189267971, 371284701189715379, 371284703376329388, 371284706497084258, 371284708274648001, 371284708275056225, 371284704899401357, 371284703859487862, 371284705144751501, 371284705145172534]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 13540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 13500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362447091482672661, 362447093861231896⟩, ⟨510078172010347569, 510099993893921591⟩, true⟩

def words05 : List Nat := [371284704125902829, 371284703107076813, 371284706500231715, 371284708245650603, 371284711649343056, 371284715052684679, 371284718457839093, 371284718458245700, 371284714628768775, 371284711854881891]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 13550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 13500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362438846115906156, 362438848498089449⟩, ⟨621901374566331911, 621923245610649219⟩, true⟩

def words06 : List Nat := [371284710903541628, 371284710903948333, 371284705496607687, 371284698977648314, 371284692459498793, 371284687604246091, 371284681448941450, 371284680712477310, 371284679975979341, 371284679245739460]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 13560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 13500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362545531522662429, 362545533908528379⟩, ⟨(-826425287250109457), (-826403366213685535)⟩, true⟩

def words07 : List Nat := [371284676431278501, 371284676994055851, 371284679731978471, 371284679732388446, 371284677664321066, 371284674828456689, 371284674566644137, 371284674981049273, 371284679462837997, 371284683944150669]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 13570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 13500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362416975871833328, 362416978261378583⟩, ⟨919758863482887773, 919780834503042453⟩, true⟩

def words08 : List Nat := [371284688427936389, 371284688428344020, 371284685843671848, 371284685984036651, 371284686055023198, 371284686055430957, 371284678923367470, 371284670752787272, 371284662583248148, 371284658970319205]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 13580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 13500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362452515625057094, 362452518018280417⟩, ⟨436884993705686188, 436907014729450696⟩, true⟩

def words09 : List Nat := [371284654407612849, 371284654824831860, 371284654986694155, 371284654987109054, 371284650700778210, 371284648081587710, 371284648235992332, 371284648236402401, 371284645895947958, 371284643534069348]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 13590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 13500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 13500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk135
