import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk625

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360554948828287387, 360554973778005842⟩, ⟨1732243071341575743, 1733296473351392859⟩, true⟩

def state01 : KState := ⟨⟨360587503217100596, 360587528175112257⟩, ⟨(-302570660462888377), (-301516740086906043)⟩, true⟩

def words00 : List Nat := [360582706078571913, 360582705900807389, 360582705903723236, 360582705906798840, 360582705907616023, 360582705695224768, 360582705227585069, 360582705016005748, 360582704804177820, 360582704756192597]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 62500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 62500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569093098721252, 360569118065082154⟩, ⟨848341227512619946, 849395669841293868⟩, true⟩

def words01 : List Nat := [360582704756974292, 360582704679388051, 360582704601641023, 360582704692117292, 360582704757038761, 360582704822101365, 360582704822900449, 360582704671326043, 360582704264593894, 360582704048284990]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 62510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 62500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576834318451843, 360576859293079237⟩, ⟨364275345921955851, 365330305111155599⟩, true⟩

def words02 : List Nat := [360582703831691840, 360582703807586301, 360582703624787215, 360582703314417254, 360582703003893041, 360582702551450936, 360582702279956163, 360582702161861648, 360582702043676766, 360582701773570380]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 62520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 62500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596349890613658, 360596374873533824⟩, ⟨(-856233368729666869), (-855177890951968235)⟩, true⟩

def words03 : List Nat := [360582701680859024, 360582701581597364, 360582701637376317, 360582701638254080, 360582701539492711, 360582701184688273, 360582700829728095, 360582700595267269, 360582700777790207, 360582700997341375]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 62530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 62500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577810909046385, 360577835900331462⟩, ⟨303087323467446856, 304143324427762000⟩, true⟩

def words04 : List Nat := [360582701089228678, 360582701090106595, 360582700927078798, 360582700717738247, 360582700508184642, 360582700124860849, 360582699702085081, 360582699150779274, 360582698599321075, 360582698303599692]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 62540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 62500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360536690411858999, 360536715411426018⟩, ⟨2875469072251152509, 2876525591287665961⟩, true⟩

def words05 : List Nat := [360582698330400052, 360582698435115468, 360582698435898385, 360582698382861850, 360582698074942247, 360582697702396876, 360582697329606358, 360582696946843282, 360582696413906741, 360582695679828954]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 62550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 62500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571192798453045, 360571217806308253⟩, ⟨716885612033095774, 717942649619619532⟩, true⟩

def words06 : List Nat := [360582694945572059, 360582694399330784, 360582693980306601, 360582693816758193, 360582693653147002, 360582693247630545, 360582692929560496, 360582692607236935, 360582692284653847, 360582692037563162]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 62560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 62500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360546285654376476, 360546310670602208⟩, ⟨2275470618474850825, 2276528179846485157⟩, true⟩

def words07 : List Nat := [360582691854966276, 360582691543954083, 360582691232796219, 360582690911363269, 360582690717068258, 360582690457313384, 360582690197480339, 360582689757519801, 360582689138076444, 360582688557784159]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 62570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 62500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360562513272013273, 360562538296510360⟩, ⟨1259885996946654967, 1260944075980405303⟩, true⟩

def words08 : List Nat := [360582687977201528, 360582687651947601, 360582687362459714, 360582686909232332, 360582686455876133, 360582685938004730, 360582685591296681, 360582685237925353, 360582684884470032, 360582684391349479]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 62580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 62500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617935869499570, 360617960902282047⟩, ⟨(-2209297725857863525), (-2208239128199928323)⟩, true⟩

def words09 : List Nat := [360582684070190951, 360582684004361774, 360582684046542392, 360582684271521597, 360582684282234779, 360582684293004686, 360582684558618544, 360582684951712855, 360582685515936956, 360582686080343102]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 62590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 62500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 62500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk625
