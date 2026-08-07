import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk304

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360557531079008571, 360557536643753486⟩, ⟨786623478852631784, 786737882929286646⟩, true⟩

def state01 : KState := ⟨⟨360592932353052649, 360592937921611836⟩, ⟨(-289814206184402906), (-289699686134736310)⟩, true⟩

def words00 : List Nat := [360583415328435833, 360583414103241551, 360583413868031353, 360583414289759163, 360583414290131199, 360583413785520209, 360583412790428451, 360583412106339036, 360583411459959947, 360583411773634633]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 30400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 30400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360554940333467663, 360554945905873376⟩, ⟨865722078391110431, 865836715431937541⟩, true⟩

def words01 : List Nat := [360583411773997896, 360583411491837929, 360583411291172273, 360583412102408514, 360583412102754560, 360583411911815934, 360583411720845904, 360583410990720485, 360583409586508624, 360583408651285340]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 30410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 30400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360611970824619462, 360611976400833374⟩, ⟨(-869436683357141003), (-869321930452127179)⟩, true⟩

def words02 : List Nat := [360583407715984160, 360583407445152599, 360583407445512475, 360583406996235056, 360583406546921773, 360583405890237275, 360583407047058195, 360583408203880262, 360583408476311411, 360583409415507486]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 30420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 30400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360641975936824684, 360641981516850024⟩, ⟨(-1782688502312045577), (-1782573633405959165)⟩, true⟩

def words03 : List Nat := [360583411430453265, 360583413445384703, 360583415771534803, 360583417022838579, 360583417349972412, 360583417677123300, 360583418170691070, 360583419354621167, 360583421278803632, 360583423202950811]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 30430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 30400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360628590121070681, 360628595704950460⟩, ⟨(-1375524958583000171), (-1375409972329286469)⟩, true⟩

def words04 : List Nat := [360583424525292382, 360583425223516575, 360583425895245672, 360583426567043405, 360583426965591373, 360583427064142104, 360583427064506517, 360583426434053150, 360583426247261848, 360583427731080003]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 30440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 30400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360528083985983489, 360528089573668613⟩, ⟨1685597148767702965, 1685712250913452805⟩, true⟩

def words05 : List Nat := [360583429816214286, 360583431901289256, 360583433448669373, 360583433922760660, 360583434124232174, 360583434325801915, 360583434326135316, 360583434115135089, 360583433223761143, 360583431407250802]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 30450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 30400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360614790567740405, 360614796159240096⟩, ⟨(-956006736390667718), (-955891518033598028)⟩, true⟩

def words06 : List Nat := [360583429590768574, 360583428569115049, 360583428232746179, 360583428377015044, 360583428377391361, 360583427620542688, 360583425791384189, 360583425035437959, 360583424596034651, 360583425626010678]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 30460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 30400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360608507150287636, 360608512745643599⟩, ⟨(-764611709479891068), (-764496373603104336)⟩, true⟩

def words07 : List Nat := [360583425813955518, 360583426001927854, 360583426823570520, 360583428185543316, 360583428893148959, 360583429600774000, 360583429772026998, 360583430019909794, 360583430843161497, 360583431666492551]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 30470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 30400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360546919474652956, 360546925073817408⟩, ⟨1112672872562020319, 1112788324541022101⟩, true⟩

def words08 : List Nat := [360583432069864256, 360583432070268947, 360583431402242272, 360583430201242263, 360583429000262662, 360583426853468511, 360583425247501138, 360583424311164520, 360583423374845041, 360583421903090646]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 30480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 30400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360622412991104789, 360622418594099652⟩, ⟨(-1189472422208262581), (-1189356853422384117)⟩, true⟩

def words09 : List Nat := [360583420706447663, 360583420581191776, 360583421401216652, 360583421616966659, 360583421617340795, 360583420955724917, 360583420702994772, 360583422008100522, 360583423287010420, 360583424565922793]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 30490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 30400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 30400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk304
