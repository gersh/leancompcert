import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk189A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk189B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk189A

def state06 : KState := ⟨⟨360443018906274415, 360443020982879812⟩, ⟨2698753945505800086, 2698780593952420032⟩, true⟩

def words05 : List Nat := [360585420621971812, 360585414469631828, 360585408317895849, 360585402585527466, 360585398603185089, 360585392811715551, 360585387020826570, 360585379515793468, 360585369239049857, 360585361731505995]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 18950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 18900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360458335311522798, 360458337390410743⟩, ⟨2408129306967404274, 2408155998702550082⟩, true⟩

def words06 : List Nat := [360585354224674425, 360585348610672891, 360585341869836225, 360585332843508830, 360585323818092335, 360585314090794335, 360585306049259683, 360585298788835335, 360585291529150034, 360585282883225849]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 18960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 18900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360536400345827442, 360536402427000956⟩, ⟨926768598466382001, 926795333569857507⟩, true⟩

def words07 : List Nat := [360585276191866733, 360585271318896380, 360585266446365864, 360585264337330599, 360585260543753850, 360585253865814898, 360585247188536826, 360585240435912774, 360585235101472245, 360585232528875027]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 18970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 18900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360492704389049651, 360492706472531448⟩, ⟨1755848081560329381, 1755874860486282023⟩, true⟩

def words08 : List Nat := [360585229956515568, 360585225383041148, 360585218044686010, 360585212291127252, 360585206538106307, 360585200085584863, 360585193269987408, 360585185071960573, 360585176874751366, 360585169603678699]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 18980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 18900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360378316557496144, 360378318643263454⟩, ⟨3928551008876192379, 3928577831215354357⟩, true⟩

def words09 : List Nat := [360585164735091297, 360585159793736678, 360585154852876888, 360585148163737395, 360585138713390103, 360585127847575594, 360585116982835716, 360585106261226280, 360585096780346127, 360585085897537947]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 18990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 18900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 18900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk189B
