import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk645

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360607279603272851, 360607306242304796⟩, ⟨(-1572829490835757185), (-1571668807840053091)⟩, true⟩

def state01 : KState := ⟨⟨360599976207260076, 360600002854834234⟩, ⟨(-1101766915007455736), (-1100605680995221814)⟩, true⟩

def words00 : List Nat := [360582940205102351, 360582940509168885, 360582940692695141, 360582940876312570, 360582940877087182, 360582940988689503, 360582941314290767, 360582941640055784, 360582941845043316, 360582942110449630]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 64500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 64500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605210229081827, 360605236885239515⟩, ⟨(-1439409394640354218), (-1438247606861787790)⟩, true⟩

def words01 : List Nat := [360582942519527802, 360582942928885827, 360582943577874685, 360582943987721009, 360582944126768689, 360582944265873798, 360582944591629962, 360582945037629680, 360582945383883199, 360582945730315355]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 64510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 64500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360609763724184566, 360609790388995092⟩, ⟨(-1733391455221108628), (-1732229109120214956)⟩, true⟩

def words02 : List Nat := [360582945927506491, 360582945928414649, 360582946035937708, 360582946186597012, 360582946212018082, 360582946368960575, 360582946384062480, 360582946399263485, 360582946608170032, 360582947025199084]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 64520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 64500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583624585899748, 360583651259276158⟩, ⟨(-46446548463412231), (-45283649563784593)⟩, true⟩

def words03 : List Nat := [360582947603802676, 360582948182568903, 360582948574485284, 360582948828057021, 360582949020977704, 360582949214133010, 360582949444498014, 360582949609668534, 360582949621357064, 360582949633184778]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 64530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 64500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591358135809399, 360591384817760131⟩, ⟨(-545560997732873141), (-544397545404658045)⟩, true⟩

def words04 : List Nat := [360582949841031700, 360582950190088162, 360582950546636663, 360582950903346139, 360582951049217764, 360582951050126486, 360582951042391865, 360582951029012782, 360582951082575314, 360582951214169100]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 64540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 64500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360599579463322300, 360599606153921722⟩, ⟨(-1076260278200731714), (-1075096267556758754)⟩, true⟩

def words05 : List Nat := [360582951225187863, 360582951236305377, 360582951486844418, 360582951942669616, 360582952337843136, 360582952733152617, 360582953004557388, 360582953225868139, 360582953484552787, 360582953743526023]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 64550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 64500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601302403456966, 360601329102625001⟩, ⟨(-1187622614102642999), (-1186458050225854943)⟩, true⟩

def words06 : List Nat := [360582953921126889, 360582953993638860, 360582953994448528, 360582953946583949, 360582953898573119, 360582953734952049, 360582953978273739, 360582954221777712, 360582954344821419, 360582954630335183]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 64560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 64500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360628176118264082, 360628202826000028⟩, ⟨(-2923089105915195718), (-2921923988766312858)⟩, true⟩

def words07 : List Nat := [360582954986321531, 360582955342559914, 360582955842406467, 360582956162865251, 360582956239547062, 360582956316273414, 360582956632229965, 360582957094462117, 360582957795812264, 360582958497346612]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 64570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 64500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605465202112658, 360605491918521266⟩, ⟨(-1456398389565159208), (-1455232712293915650)⟩, true⟩

def words08 : List Nat := [360582958996007860, 360582959504077833, 360582959985416311, 360582960467020311, 360582960888032268, 360582961159654835, 360582961310939251, 360582961462318317, 360582961607648659, 360582961957500475]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 64580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 64500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360573658087792721, 360573684812763955⟩, ⟨598287019942934006, 599453250317211438⟩, true⟩

def words09 : List Nat := [360582962546341149, 360582963135343811, 360582963604176861, 360582963834391989, 360582964004191467, 360582964174243932, 360582964414747152, 360582964416733195, 360582964417543475, 360582964274843169]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 64590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 64500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 64500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk645
