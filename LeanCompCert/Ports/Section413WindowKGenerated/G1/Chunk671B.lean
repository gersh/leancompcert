import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk671A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk671B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk671A

def state06 : KState := ⟨⟨362508133771320427, 362508200493805148⟩, ⟨(-1526547374343897627), (-1523520873472451807)⟩, true⟩

def words05 : List Nat := [371285514409390774, 371285514536213410, 371285514883255366, 371285514935669547, 371285514937455978, 371285514908696925, 371285515069220824, 371285515207358797, 371285515546693092, 371285515887062062]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497963498600634, 362498030241739452⟩, ⟨(-843528274871842902), (-840500386764939498)⟩, true⟩

def words06 : List Nat := [371285516209354320, 371285516236927692, 371285516447984482, 371285516660199729, 371285516867903363, 371285516916581575, 371285516939317876, 371285516962838875, 371285517206718162, 371285517395618881]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476377117327442, 362476443881105346⟩, ⟨606612556022900796, 609641830564191396⟩, true⟩

def words07 : List Nat := [371285517730198342, 371285518065715214, 371285518400808706, 371285518441299244, 371285518547513897, 371285518654905515, 371285518856542983, 371285518858835515, 371285518765503970, 371285518632974418]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362498831971352174, 362498898755655377⟩, ⟨(-901991297111334694), (-898960643575554298)⟩, true⟩

def words08 : List Nat := [371285518585609764, 371285518588136022, 371285518682256728, 371285518802123636, 371285518886415945, 371285518888748634, 371285518907690894, 371285519029723522, 371285519371773172, 371285519573271196]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481330320194613, 362481397125445341⟩, ⟨274074365175948431, 277106426275088519⟩, true⟩

def words09 : List Nat := [371285519774486986, 371285519976492762, 371285520223900857, 371285520362516949, 371285520543517965, 371285520725371094, 371285520904819192, 371285520907112339, 371285520791414455, 371285520732979197]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk671B
