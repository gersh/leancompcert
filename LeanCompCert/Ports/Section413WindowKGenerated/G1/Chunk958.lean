import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk958

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481120685507453, 362481260232321277⟩, ⟨372972259140740142, 381998200051189394⟩, true⟩

def state01 : KState := ⟨⟨362493983948636236, 362494123525554272⟩, ⟨(-859355607223845919), (-850326782175578623)⟩, true⟩

def words00 : List Nat := [371285247715574771, 371285247746994574, 371285247886025882, 371285248026393691, 371285248147374480, 371285248150733669, 371285248195590477, 371285248269175713, 371285248386014350, 371285248482164937]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 95800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 95800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500635588331760, 362500775195787626⟩, ⟨(-1496674358405971924), (-1487642607370461634)⟩, true⟩

def words01 : List Nat := [371285248580026774, 371285248679001656, 371285248885704431, 371285249039276035, 371285249224200381, 371285249410507265, 371285249583767410, 371285249640095333, 371285249804401263, 371285249970551296]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 95810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 95800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491700211128223, 362491839848541512⟩, ⟨(-640460637433146366), (-631426015723333804)⟩, true⟩

def words02 : List Nat := [371285250181109335, 371285250247483355, 371285250296321223, 371285250346256198, 371285250428291409, 371285250457486993, 371285250582828186, 371285250709504933, 371285250822609317, 371285250894907267]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 95820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 95800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502420547321067, 362502560215134437⟩, ⟨(-1667838613351747605), (-1658801078251504713)⟩, true⟩

def words03 : List Nat := [371285251058556260, 371285251224041248, 371285251479224166, 371285251590278590, 371285251684246557, 371285251779255093, 371285251917932881, 371285252003830742, 371285252186703620, 371285252371119334]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 95830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 95800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488497347650230, 362488637045801160⟩, ⟨(-333400256322380143), (-324359813519384971)⟩, true⟩

def words04 : List Nat := [371285252546887730, 371285252591345169, 371285252690188696, 371285252790792974, 371285252912725497, 371285252924474623, 371285252932962131, 371285252942614679, 371285253006309123, 371285253045493189]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 95840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 95800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488569383266616, 362488709111662850⟩, ⟨(-340299925640007438), (-331256583666192264)⟩, true⟩

def words05 : List Nat := [371285253128109156, 371285253212024991, 371285253290678332, 371285253294062092, 371285253278843575, 371285253286547283, 371285253401445563, 371285253440461875, 371285253479046100, 371285253518839218]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495355639610844, 362495495398065306⟩, ⟨(-990838939634824488), (-981792716123668098)⟩, true⟩

def words06 : List Nat := [371285253656493647, 371285253753990828, 371285253918240291, 371285254083884741, 371285254214547688, 371285254217909231, 371285254270059422, 371285254341064766, 371285254519273507, 371285254629573023]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493178472786381, 362493318261955630⟩, ⟨(-782062254986381252), (-773013086702607998)⟩, true⟩

def words07 : List Nat := [371285254738413836, 371285254848502064, 371285255066048357, 371285255252582133, 371285255447972001, 371285255644626084, 371285255831347018, 371285255873814122, 371285255960221382, 371285256048517070]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486855218464266, 362486995037575291⟩, ⟨(-175729902913989532), (-166677863656380850)⟩, true⟩

def words08 : List Nat := [371285256243804345, 371285256305397931, 371285256368151587, 371285256432008171, 371285256519480638, 371285256569406102, 371285256650774380, 371285256733553534, 371285256814636968, 371285256836246112]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494715884417737, 362494855733902724⟩, ⟨(-929532252444872478), (-920477300473486876)⟩, true⟩

def words09 : List Nat := [371285256965559230, 371285257096578985, 371285257250724292, 371285257260875046, 371285257263500639, 371285257255599433, 371285257302901742, 371285257324272095, 371285257426640274, 371285257530542244]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk958
