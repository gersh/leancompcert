import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk786A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362487701314674750, 362487793828840179⟩, ⟨(-206215276049483873), (-201304929713790291)⟩, true⟩

def state01 : KState := ⟨⟨362486843367919054, 362486935906294077⟩, ⟨(-138781533155806231), (-133869283820288177)⟩, true⟩

def words00 : List Nat := [371285232910288771, 371285232913002846, 371285232877851178, 371285232816827468, 371285232754789304, 371285232742200458, 371285232762937500, 371285232856241550, 371285232948546150, 371285232973068189]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 78600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 78600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362495663902506802, 362495756465347858⟩, ⟨(-832188818076697274), (-827274645337809830)⟩, true⟩

def words01 : List Nat := [371285233103432075, 371285233235161840, 371285233511193706, 371285233614028841, 371285233691692569, 371285233770206500, 371285233865680444, 371285233881392399, 371285234017076210, 371285234153938212]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 78610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 78600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485638046225836, 362485730633594718⟩, ⟨(-43932053885556851), (-39015952652843247)⟩, true⟩

def words02 : List Nat := [371285234289664790, 371285234292385521, 371285234387662450, 371285234518609309, 371285234646311349, 371285234649026272, 371285234561310084, 371285234474474557, 371285234433719464, 371285234443127182]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 78620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 78600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470221992531884, 362470314604384626⟩, ⟨1168331861461631357, 1173249887988190419⟩, true⟩

def words03 : List Nat := [371285234499978760, 371285234557925505, 371285234614412317, 371285234617127547, 371285234457987548, 371285234349734943, 371285234240118328, 371285234198752582, 371285234041879722, 371285233855249176]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 78630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 78600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483755846119124, 362483848482275920⟩, ⟨103974980825674720, 108894918744989580⟩, true⟩

def words04 : List Nat := [371285233667381498, 371285233600319538, 371285233491318787, 371285233519610330, 371285233521749192, 371285233509933348, 371285233281826867, 371285233145667952, 371285233030207157, 371285233033054623]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 78640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 78600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk786A
