import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk021

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360682307186196367, 360682307206396423⟩, ⟨(-241725346747096824), (-241725317890398796)⟩, true⟩

def state01 : KState := ⟨⟨359870325648821194, 359870325669224565⟩, ⟨1466330219220569870, 1466330248505249418⟩, true⟩

def words00 : List Nat := [360567326022454922, 360567326022476469, 360567177341172043, 360566913773307132, 360566650455859557, 360566322939894067, 360566137383571579, 360565901685926277, 360565666211794705, 360565268914961651]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 2100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 2100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360951647050601731, 360951647071209785⟩, ⟨(-819269398858568093), (-819269369140976015)⟩, true⟩

def words01 : List Nat := [360564939714010170, 360564830679481599, 360564832570528295, 360564968161585440, 360564968161605600, 360564910238138204, 360564876114238457, 360565016882806722, 360565199255554811, 360565381456338981]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 2110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 2100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360054395068649754, 360054395089465682⟩, ⟨1081599621568457042, 1081599651727779176⟩, true⟩

def words02 : List Nat := [360565382663713228, 360565382663735002, 360565168663558281, 360564973421040973, 360564778362275561, 360564455491289734, 360563918110280726, 360563268924753713, 360562620349072445, 360562188353187645]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 2120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 2100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨359614397579259584, 359614397600281772⟩, ⟨2024021672395737146, 2024021702995448548⟩, true⟩

def words03 : List Nat := [360561950064484749, 360561927771588360, 360561905499592583, 360561763430334399, 360561625267150308, 360561325374373074, 360561025762256687, 360560941345271362, 360560644305726792, 360560202134391795]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 2130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 2100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360712446102653086, 360712446123884049⟩, ⟨(-328294803592169726), (-328294772544660646)⟩, true⟩

def words04 : List Nat := [360559760376103217, 360559533488817032, 360559684272709509, 360559866640095703, 360559866640116247, 360559838391860492, 360559766200518418, 360559766778092990, 360559766778111291, 360559821868865611]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 2140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 2100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360820305240567835, 360820305262010373⟩, ⟨(-560267330601011089), (-560267299097545055)⟩, true⟩

def words05 : List Nat := [360559821868885578, 360559777925462157, 360559902167483330, 360560182724482608, 360560401516674749, 360560620106003827, 360560728688308054, 360560802112778473, 360560922253143458, 360561042282326179]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 2150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 2100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361087970144723982, 361087970166377152⟩, ⟨(-1140113262189346833), (-1140113230229847645)⟩, true⟩

def words06 : List Nat := [360561372339812955, 360561651110677167, 360561759556768909, 360561867902681590, 360561916199261299, 360562092823300583, 360562289943565619, 360562486882073302, 360562572364404431, 360562814371706564]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 2160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 2100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361265655461228282, 361265655483093289⟩, ⟨(-1529086394197880189), (-1529086361777639265)⟩, true⟩

def words07 : List Nat := [360563099561333437, 360563384488481933, 360563746040330286, 360563902263051361, 360563902263072091, 360563873801121845, 360563845365315552, 360563917822759185, 360564239720786771, 360564561323635408]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 2170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 2100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360191069263655683, 360191069285735463⟩, ⟨815689083241463565, 815689116130975321⟩, true⟩

def words08 : List Nat := [360564775368807123, 360564785335753666, 360564865347528947, 360564945286073804, 360564945286092820, 360564882796655527, 360564616844784936, 360564246646215617, 360563876785877571, 360563530069356913]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 2180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 2100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨359206063556680520, 359206063578974424⟩, ⟨2977018270295678242, 2977018303655212604⟩, true⟩

def words09 : List Nat := [360563360073582087, 360563176887383776, 360562993868247620, 360562653818468351, 360562111427221464, 360561512731754523, 360560914581292832, 360560379839268309, 360559869083114130, 360559253716999521]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 2190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 2100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 2100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk021
