import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk950

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493650236233399, 362493787373195418⟩, ⟨(-824111183115360481), (-815315143650100235)⟩, true⟩

def state01 : KState := ⟨⟨362486788537598958, 362486925704601040⟩, ⟨(-172251909340771050), (-163453015917835538)⟩, true⟩

def words00 : List Nat := [371285205291327385, 371285205294656672, 371285205292336475, 371285205349574841, 371285205438435133, 371285205441765022, 371285205399853018, 371285205339236481, 371285205323832343, 371285205345738195]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 95000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 95000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478623947712531, 362478761144688911⟩, ⟨603507489661780822, 612309231096353320⟩, true⟩

def words01 : List Nat := [371285205410541921, 371285205476630064, 371285205521963255, 371285205525292885, 371285205422761618, 371285205350111967, 371285205275714830, 371285205275597640, 371285205212491932, 371285205148383885]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 95010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 95000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488197087363416, 362488334314127193⟩, ⟨(-306145568189762528), (-297340996203695542)⟩, true⟩

def words02 : List Nat := [371285205125869871, 371285205129574182, 371285205204556056, 371285205293319874, 371285205356294237, 371285205359624241, 371285205298142754, 371285205325645507, 371285205393507978, 371285205429908321]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 95020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 95000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489465391439924, 362489602648659406⟩, ⟨(-426662071357394436), (-417854605025659288)⟩, true⟩

def words03 : List Nat := [371285205465720786, 371285205502728159, 371285205618388440, 371285205687807478, 371285205782900051, 371285205879242214, 371285205973719242, 371285205977531678, 371285206026090566, 371285206076600762]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 95030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 95000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483483053807936, 362483620340654840⟩, ⟨141946870505951028, 150757152783952876⟩, true⟩

def words04 : List Nat := [371285206219168750, 371285206222499621, 371285206217712982, 371285206213751616, 371285206234315928, 371285206238054503, 371285206296753660, 371285206363473148, 371285206419819347, 371285206423272241]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 95040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 95000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362485964193877214, 362486101510843280⟩, ⟨(-93917806228520569), (-85104660970883269)⟩, true⟩

def words05 : List Nat := [371285206448459674, 371285206492010256, 371285206562685106, 371285206566016481, 371285206489412610, 371285206397123867, 371285206303423978, 371285206292405001, 371285206233964557, 371285206247160268]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 95050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 95000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478983515373583, 362479120862360434⟩, ⟨569706204319103947, 578522203508299325⟩, true⟩

def words06 : List Nat := [371285206258701930, 371285206262059311, 371285206238319263, 371285206284723966, 371285206362758373, 371285206366090068, 371285206296828611, 371285206207875028, 371285206117607962, 371285206085916849]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 95060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 95000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475681047694546, 362475818424700193⟩, ⟨883737752217231110, 892556605446697818⟩, true⟩

def words07 : List Nat := [371285206070896356, 371285206121286086, 371285206137333351, 371285206140723652, 371285206064713087, 371285206024346158, 371285206030492574, 371285206033824861, 371285205947145458, 371285205852187012]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 95070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 95000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483862986657960, 362484000393546619⟩, ⟨105751960384995029, 114573655041577101⟩, true⟩

def words08 : List Nat := [371285205755762027, 371285205674970576, 371285205559168752, 371285205555430530, 371285205550684145, 371285205528307291, 371285205357401638, 371285205299045606, 371285205287087212, 371285205290539380]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 95080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 95000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485820623173871, 362485958060363817⟩, ⟨(-80402275822684006), (-71577699661356334)⟩, true⟩

def words09 : List Nat := [371285205280361133, 371285205265138900, 371285205340474027, 371285205381317791, 371285205411143828, 371285205442202518, 371285205471735272, 371285205475077481, 371285205399067316, 371285205411078727]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 95090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 95000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 95000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk950
