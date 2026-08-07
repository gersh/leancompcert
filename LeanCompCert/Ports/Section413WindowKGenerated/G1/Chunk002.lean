import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk002

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨371132091258236268, 371132091258547978⟩, ⟨(-1738994481489300173), (-1738994481446662291)⟩, true⟩

def state01 : KState := ⟨⟨360664288500707666, 360664288501053954⟩, ⟨394326923123067033, 394326923172802681⟩, true⟩

def words00 : List Nat := [371321436070408247, 371331218582720254, 371346722221258464, 371362074604788327, 371381100394740359, 371381100394744191, 371370501540166654, 371358267349340736, 371346150232109774, 371342035754257777]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨356334713629399427, 356334713629782835⟩, ⟨1350484406022898159, 1350484406080624691⟩, true⟩

def words01 : List Nat := [371345515993668098, 371357779269579394, 371369273126488363, 371369273126492447, 371353448629727536, 371342990974029556, 371332629702253099, 371329965074955192, 371301309091333521, 371273279111967493]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨359837796857139996, 359837796857562571⟩, ⟨564426723357810269, 564426723424359385⟩, true⟩

def words02 : List Nat := [371245502797571433, 371226649613527790, 371198424562375572, 371188724922209334, 371179111501065475, 371166461617401132, 371129779412697037, 371111114576485266, 371092612751941411, 371091826089842395]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨363070266672016797, 363070266672481541⟩, ⟨(-202175375365541156), (-202175375289074088)⟩, true⟩

def words03 : List Nat := [371081202586675834, 371064338716198746, 371048339749737767, 371048339749742833, 371042151363884316, 371040524432088801, 371038911229674139, 371037368638187472, 371027869275437962, 371031364700327707]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361040593648121613, 361040593648628989⟩, ⟨310448882175013724, 310448882261939830⟩, true⟩

def words04 : List Nat := [371051142503055981, 371055447153942770, 371059716520804780, 371063951035693869, 371068971281941292, 371068971281946527, 371071813976452741, 371077113032983300, 371082389177671744, 371082389177676749]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨363146275449903151, 363146275450455505⟩, ⟨(-220151672644836693), (-220151672546434397)⟩, true⟩

def words05 : List Nat := [371087559878418973, 371097597986782495, 371112568695535243, 371112568695540145, 371108050371273336, 371099576336192898, 371097165602712700, 371097165602718197, 371099538248348232, 371102782452193305]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362687965285574674, 362687965286174091⟩, ⟨(-113735196274254611), (-113735196163369221)⟩, true⟩

def words06 : List Nat := [371104971959385165, 371104971959390290, 371088875969521225, 371086595202203793, 371085696022431327, 371085696022436614, 371077842059582675, 371069712263961033, 371066723818896344, 371068278215460552]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360151482315740632, 360151482316388804⟩, ⟨598735504080543394, 598735504204849494⟩, true⟩

def words07 : List Nat := [371082819618246995, 371097254490612201, 371109525607603386, 371109525607608739, 371104863158802991, 371100838851700306, 371105409863604290, 371105409863609735, 371097487707797819, 371089823402834696]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨364295913408160113, 364295913408858819⟩, ⟨(-565976041991258311), (-565976041852534331)⟩, true⟩

def words08 : List Nat := [371086867555777342, 371086867555783372, 371097545260447916, 371108891065202930, 371118896476218040, 371121225052354601, 371126411724218394, 371131562502162131, 371144271885223463, 371150978557131897]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨363297956301138701, 363297956301890753⟩, ⟨(-259017119865512800), (-259017119711038714)⟩, true⟩

def words09 : List Nat := [371156613238108187, 371162209457100148, 371179212013051581, 371191895901962183, 371206658502116397, 371221321690823979, 371233726168208473, 371233726168214357, 371234565902846820, 371237434309495276]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk002
