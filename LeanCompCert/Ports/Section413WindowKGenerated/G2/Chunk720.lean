import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk720

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360594655305928246, 360594688792299822⟩, ⟨(-890678283824524270), (-889049763511985660)⟩, true⟩

def state01 : KState := ⟨⟨360603991533362573, 360604025029371675⟩, ⟨(-1562890140457069208), (-1561260926195053246)⟩, true⟩

def words00 : List Nat := [360582341367570232, 360582341747773411, 360582342031632121, 360582342315594661, 360582342550365312, 360582342930624235, 360582343291387828, 360582343652332437, 360582343860054420, 360582344162195896]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360612689543963754, 360612723049619837⟩, ⟨(-2189327411186824457), (-2187697502197301603)⟩, true⟩

def words01 : List Nat := [360582344619059638, 360582345076213595, 360582345536575428, 360582345804629340, 360582345908509802, 360582346012484635, 360582346145835205, 360582346376265874, 360582346798873384, 360582347221705794]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573245240655500, 360573278756056971⟩, ⟨651551958444721379, 653182569344864295⟩, true⟩

def words02 : List Nat := [360582347548220436, 360582347682380481, 360582347812378870, 360582347942659168, 360582347974589604, 360582347975611823, 360582347815157689, 360582347540064094, 360582347264779595, 360582346957769381]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360531950944790282, 360531984469814703⟩, ⟨3626304772143744935, 3627936076232677465⟩, true⟩

def words03 : List Nat := [360582346899244268, 360582346966806068, 360582346967721305, 360582346912677092, 360582346665053545, 360582346368765484, 360582346072186345, 360582345709878695, 360582345191090502, 360582344493082786]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589131927909502, 360589165462587630⟩, ⟨(-493337101295756409), (-491705101706938529)⟩, true⟩

def words04 : List Nat := [360582343794863002, 360582343232444202, 360582342766714355, 360582342493579118, 360582342220362231, 360582341783943028, 360582341395013138, 360582341198747813, 360582341002185476, 360582341059016453]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360586918095183215, 360586951639605180⟩, ⟨(-333808704853546874), (-332176003171563634)⟩, true⟩

def words05 : List Nat := [360582341059943961, 360582341003219659, 360582341080873241, 360582341313189153, 360582341496311986, 360582341679596460, 360582341766752382, 360582341859463993, 360582341924267504, 360582341989403663]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 72050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 72000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566392634102950, 360566426188148276⟩, ⟨1145305782285087422, 1146939177475339632⟩, true⟩

def words06 : List Nat := [360582342083847276, 360582342084870124, 360582342034883808, 360582341844102294, 360582341653175233, 360582341298703103, 360582341040835291, 360582340868153303, 360582340695364327, 360582340426770107]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 72060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 72000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586854795252154, 360586888358973640⟩, ⟨(-329501669852968655), (-327867577256659025)⟩, true⟩

def words07 : List Nat := [360582340206783984, 360582340127784141, 360582340160464360, 360582340161487362, 360582340082285841, 360582339844155217, 360582339605834873, 360582339631681486, 360582339695629988, 360582339759796927]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 72070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 72000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592107489873922, 360592141063345118⟩, ⟨(-708292291181101770), (-706657495777780796)⟩, true⟩

def words08 : List Nat := [360582339760717057, 360582339727872855, 360582339606394972, 360582339514905615, 360582339423151874, 360582339227843492, 360582339101943023, 360582338880248598, 360582338658364475, 360582338764919826]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 72080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 72000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594058528842657, 360594092111964864⟩, ⟨(-848902657557929861), (-847267166365400159)⟩, true⟩

def words09 : List Nat := [360582339093819475, 360582339422906055, 360582339601926149, 360582339823605136, 360582339996278750, 360582340169218697, 360582340407763597, 360582340668664497, 360582340832572936, 360582340996635460]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 72090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 72000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 72000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk720
