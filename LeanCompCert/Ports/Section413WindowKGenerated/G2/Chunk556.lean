import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk556

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360551232321190613, 360551251882665143⟩, ⟨1701583477380942304, 1702318315304326724⟩, true⟩

def state01 : KState := ⟨⟨360565000938489187, 360565020507275487⟩, ⟨935902294357899594, 936637538852088000⟩, true⟩

def words00 : List Nat := [360581868568531658, 360581867858826424, 360581867311318466, 360581867086503376, 360581866861640927, 360581866313544445, 360581865442865957, 360581864680124174, 360581863917168233, 360581863476864628]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 55600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 55600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360552362690322212, 360552382266482142⟩, ⟨1638759383487525182, 1639495038064781296⟩, true⟩

def words01 : List Nat := [360581863174689527, 360581862655960348, 360581862137103014, 360581861762152895, 360581861630655613, 360581861262465391, 360581860894198671, 360581860364965047, 360581859513259016, 360581858984174785]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 55610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 55600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360556682160868659, 360556701744324963⟩, ⟨1398596498141447887, 1399332558579826265⟩, true⟩

def words02 : List Nat := [360581858454843810, 360581858248008056, 360581858160838282, 360581857912745776, 360581857664534660, 360581857303380519, 360581857126848068, 360581856842038801, 360581856557173731, 360581856023645111]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 55620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 55600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589588821117013, 360589608411879349⟩, ⟨(-432186420253839988), (-431449953344840150)⟩, true⟩

def words03 : List Nat := [360581855572107854, 360581855443026553, 360581855505993353, 360581855506767386, 360581855377548263, 360581854972907596, 360581854568121089, 360581854141272575, 360581854098469247, 360581854238637588]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 55630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 55600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360549644243549899, 360549663841692012⟩, ⟨1790386793087751899, 1791123670642775827⟩, true⟩

def words04 : List Nat := [360581854239329064, 360581854155143572, 360581853869396673, 360581853576387090, 360581853283183456, 360581852850172270, 360581852095039319, 360581851164258444, 360581850233366321, 360581849352395387]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 55640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 55600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360499136291599009, 360499155897031539⟩, ⟨4601416249608724208, 4602153532912712096⟩, true⟩

def words05 : List Nat := [360581848774677708, 360581848180133474, 360581847585529365, 360581846781115002, 360581845654612686, 360581844447183077, 360581843239572769, 360581842024734464, 360581840700709869, 360581839215984337]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 55650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 55600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360564208911300994, 360564228524035342⟩, ⟨979152713820646962, 979890403580838754⟩, true⟩

def words06 : List Nat := [360581837731130188, 360581836568459615, 360581835567647144, 360581834888924280, 360581834210158303, 360581833257088650, 360581832209691895, 360581831484416828, 360581830758940709, 360581830291658494]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 55660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 55600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360565018901259936, 360565038521382455⟩, ⟨934011088851481131, 934749189947712379⟩, true⟩

def words07 : List Nat := [360581829976190404, 360581829358862231, 360581828741407895, 360581828445992311, 360581828313335478, 360581827974368337, 360581827635328369, 360581827100636655, 360581826702576752, 360581826401949045]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 55670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 55600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360569573590996028, 360569593218406521⟩, ⟨680407229540049463, 681145736468248177⟩, true⟩

def words08 : List Nat := [360581826121281686, 360581826122061652, 360581826095941798, 360581825860093748, 360581825624139682, 360581825104738787, 360581824746959984, 360581824645227431, 360581824543415454, 360581824242584439]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 55680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 55600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574073628161445, 360574093262899587⟩, ⟨429778498818542786, 430517413858254434⟩, true⟩

def words09 : List Nat := [360581824125555239, 360581824228401937, 360581824280888183, 360581824281663205, 360581824012760966, 360581823462995208, 360581822913100644, 360581822684981129, 360581822618347935, 360581822480383578]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 55690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 55600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 55600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk556
