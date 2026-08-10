import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk773A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502708681257630, 362502798045229181⟩, ⟨(-1364614783448658592), (-1359950001057379396)⟩, true⟩

def state01 : KState := ⟨⟨362486018997390207, 362486108385451530⟩, ⟨(-74474091945105185), (-69807447290350603)⟩, true⟩

def words00 : List Nat := [371285205323220611, 371285205325886884, 371285205384397173, 371285205475276135, 371285205615997254, 371285205618663600, 371285205536607819, 371285205455143393, 371285205427430011, 371285205442179676]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 77300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 77300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476682107491817, 362476771519570626⟩, ⟨647450154412409451, 652118655980650123⟩, true⟩

def words01 : List Nat := [371285205532137653, 371285205623204572, 371285205713467266, 371285205716139421, 371285205670366154, 371285205631986405, 371285205717818499, 371285205720485786, 371285205648600279, 371285205542539854]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 77310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 77300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495260023702132, 362495349459708478⟩, ⟨(-789043800077437131), (-784373448314928891)⟩, true⟩

def words02 : List Nat := [371285205478359020, 371285205481349854, 371285205616759156, 371285205769988620, 371285205895956028, 371285205898628037, 371285205971584321, 371285206081561087, 371285206259606895, 371285206393560169]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 77320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 77300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496044610276946, 362496134070515627⟩, ⟨(-849715084526543942), (-845042858749391960)⟩, true⟩

def words03 : List Nat := [371285206516974238, 371285206641261863, 371285206870473375, 371285207017156720, 371285207213944342, 371285207411823381, 371285207610810462, 371285207613477975, 371285207730821097, 371285207875370111]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 77330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 77300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485052158782048, 362485141642832600⟩, ⟨459236515039329, 5133304022844989⟩, true⟩

def words04 : List Nat := [371285208083103120, 371285208085770825, 371285208071020647, 371285208011113218, 371285207950149160, 371285207933502753, 371285207897276430, 371285207964626712, 371285208004626714, 371285208007461209]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 77340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 77300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk773A
