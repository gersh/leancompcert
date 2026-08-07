import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk831

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592247520535214, 360592292632941160⟩, ⟨(-822156981438836919), (-819625212890799899)⟩, true⟩

def state01 : KState := ⟨⟨360593242076776861, 360593287200404218⟩, ⟨(-904801627803878978), (-902268926700944496)⟩, true⟩

def words00 : List Nat := [360582429896724143, 360582430077614452, 360582430185709115, 360582430293952528, 360582430307685965, 360582430408985350, 360582430595499286, 360582430782236820, 360582430877106889, 360582431008965047]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 83100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 83100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360606815193489834, 360606860328378805⟩, ⟨(-2033025106573012223), (-2030491469461127443)⟩, true⟩

def words01 : List Nat := [360582431105041576, 360582431201448277, 360582431345901303, 360582431414771499, 360582431415881189, 360582431361156722, 360582431394956351, 360582431597858122, 360582431892719219, 360582432187843187]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 83110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 83100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360603793750368246, 360603838896608266⟩, ⟨(-1781938590210957771), (-1779404009545402753)⟩, true⟩

def words02 : List Nat := [360582432399905652, 360582432636505479, 360582432980430511, 360582433324709644, 360582433558392139, 360582433682898137, 360582433693173796, 360582433703571919, 360582433818743366, 360582434077593153]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 83120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 83100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589110316564772, 360589155474043219⟩, ⟨(-561198861778873774), (-558663346805785626)⟩, true⟩

def words03 : List Nat := [360582434431832508, 360582434786312396, 360582435067819418, 360582435233396835, 360582435318552032, 360582435404016700, 360582435633735592, 360582435841387877, 360582435923292389, 360582436005347801]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 83130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 83100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599705545338602, 360599750714078192⟩, ⟨(-1442104163418761309), (-1439567712140282475)⟩, true⟩

def words04 : List Nat := [360582436190846226, 360582436463394221, 360582436749041411, 360582437034911471, 360582437184915791, 360582437338324743, 360582437488669045, 360582437639363936, 360582437811914488, 360582438021360844]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 83140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 83100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360586961362864508, 360587006542983243⟩, ⟨(-382369584936186493), (-379832187427673399)⟩, true⟩

def words05 : List Nat := [360582438158123243, 360582438295002395, 360582438427748309, 360582438633162724, 360582438801879900, 360582438970787597, 360582439056980846, 360582439058173515, 360582439054954016, 360582439111285360]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 83150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 83100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575369348239296, 360575414539577357⟩, ⟨581660988935826464, 584199319501526990⟩, true⟩

def words06 : List Nat := [360582439210559205, 360582439220061839, 360582439221126857, 360582439142129914, 360582439062937094, 360582438947714173, 360582438913926259, 360582438866377273, 360582438818707622, 360582438698763380]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 83160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 83100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607018225467136, 360607063428061982⟩, ⟨(-2050788671942911719), (-2048249405093577793)⟩, true⟩

def words07 : List Nat := [360582438615279798, 360582438554386255, 360582438518033521, 360582438604926538, 360582438606028031, 360582438571494324, 360582438645459132, 360582438828246817, 360582439125251068, 360582439422518726]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 83170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 83100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602304644908513, 360602349858882500⟩, ⟨(-1658762359459549769), (-1656222146038986205)⟩, true⟩

def words08 : List Nat := [360582439586547980, 360582439786831550, 360582440105566588, 360582440424644366, 360582440684954683, 360582440801302521, 360582440821818003, 360582440842467565, 360582440948444576, 360582441189122082]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 83180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 83100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578339455780742, 360578384680987999⟩, ⟨335029647978704581, 337570795953313029⟩, true⟩

def words09 : List Nat := [360582441497273351, 360582441805644493, 360582442004154265, 360582442058656358, 360582442059672365, 360582442015505772, 360582442043824434, 360582442068746353, 360582442069809563, 360582442022285515]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 83190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 83100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 83100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk831
