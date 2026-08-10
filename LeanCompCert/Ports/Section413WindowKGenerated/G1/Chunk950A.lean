import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk950A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk950A
