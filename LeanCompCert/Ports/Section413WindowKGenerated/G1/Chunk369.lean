import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk369

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489763739111070, 362489782933678209⟩, ⟨(-182099443998029158), (-181620783783974232)⟩, true⟩

def state01 : KState := ⟨⟨362458979700892021, 362458998906163790⟩, ⟨954066161361714525, 954545216633558719⟩, true⟩

def words00 : List Nat := [371284861962871266, 371284861964074374, 371284861853797353, 371284861741541068, 371284861628803312, 371284861502148498, 371284861009996233, 371284860787754497, 371284860565138968, 371284860331702494]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 36900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 36900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484636057829001, 362484655274008374⟩, ⟨6918861603089061, 7398319529137493⟩, true⟩

def words01 : List Nat := [371284859631890450, 371284859235139951, 371284859173236488, 371284859174439899, 371284858532864327, 371284857711037080, 371284856888770216, 371284856403984241, 371284855665920162, 371284855661861276]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 36910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 36900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362459822507174094, 362459841734196970⟩, ⟨923074002612589467, 923553860936886353⟩, true⟩

def words02 : List Nat := [371284855657334289, 371284855653089375, 371284854670874174, 371284854422621733, 371284854173813743, 371284853950943081, 371284852888665334, 371284851668895750, 371284850448686077, 371284849962221257]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 36920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 36900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362460017922782133, 362460037160651736⟩, ⟨915959111372614620, 916439370321307608⟩, true⟩

def words03 : List Nat := [371284849341820416, 371284849399078136, 371284849441107894, 371284849442312297, 371284848613526404, 371284847951590161, 371284847289038873, 371284847227020280, 371284846693145407, 371284846022869422]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 36930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 36900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491886024184133, 362491905272830734⟩, ⟨(-261360194107552091), (-260879537000878999)⟩, true⟩

def words04 : List Nat := [371284845352108848, 371284844942141010, 371284844252712824, 371284844275279392, 371284844276220081, 371284844170213920, 371284843999614566, 371284844281619877, 371284844932286097, 371284845124607388]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 36940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 36900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362484199129501888, 362484218389159260⟩, ⟨22736289677328063, 23217353683913679⟩, true⟩

def words05 : List Nat := [371284845336927191, 371284845549653550, 371284846063248209, 371284846210478723, 371284846527393419, 371284846844739310, 371284847083900883, 371284847085109105, 371284846579764415, 371284846564313046]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 36950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 36900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362454496218571638, 362454515488933187⟩, ⟨1120744966494365742, 1121226426184805746⟩, true⟩

def words06 : List Nat := [371284847055482949, 371284847056688044, 371284846589298548, 371284846055828263, 371284845521936757, 371284845209392674, 371284844555332711, 371284844203269410, 371284843850808055, 371284843496133209]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 36960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 36900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507510976584323, 362507530257832734⟩, ⟨(-839499021416072697), (-839017159183736677)⟩, true⟩

def words07 : List Nat := [371284842676637931, 371284842227194417, 371284842057701606, 371284842058930556, 371284841877572466, 371284841493623803, 371284841354975312, 371284841356303161, 371284841853050611, 371284842467908618]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 36970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 36900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486471414659324, 362486490706805838⟩, ⟨(-61414244612307733), (-60931979313493833)⟩, true⟩

def words08 : List Nat := [371284842917301594, 371284842918515892, 371284843270142215, 371284843751783376, 371284844350250045, 371284844351455812, 371284843975654594, 371284843597855301, 371284843449961481, 371284843495881195]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 36980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 36900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472300166310937, 362472319469320199⟩, ⟨462919834009119033, 463402501175689635⟩, true⟩

def words09 : List Nat := [371284844168827777, 371284844842248477, 371284845313415041, 371284845314621372, 371284844929374631, 371284844556160594, 371284844538102185, 371284844539314055, 371284844198382606, 371284843861243867]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 36990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 36900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 36900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk369
