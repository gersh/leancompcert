import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk603A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588904117829615, 360588927276161632⟩, ⟨(-399777106548701636), (-398833708394500074)⟩, true⟩

def state01 : KState := ⟨⟨360594821600635715, 360594844766910349⟩, ⟨(-756642136824005963), (-755698259689689893)⟩, true⟩

def words00 : List Nat := [360582313523852165, 360582313777404340, 360582313892495552, 360582314007675265, 360582314008393793, 360582314060400262, 360582314264233666, 360582314468218893, 360582314534570569, 360582314743205060]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360606283058697884, 360606306232952942⟩, ⟨(-1447963257058931270), (-1447018898585841686)⟩, true⟩

def words01 : List Nat := [360582315111769703, 360582315480585716, 360582315890528183, 360582316119773616, 360582316120551906, 360582316117504876, 360582316385336351, 360582316793580896, 360582317191978295, 360582317590546718]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596780032064458, 360596803214353306⟩, ⟨(-874810968083932148), (-873866124972823794)⟩, true⟩

def words02 : List Nat := [360582317850694635, 360582317851538922, 360582318040798463, 360582318244758175, 360582318303482434, 360582318440280202, 360582318441039222, 360582318440436226, 360582318444204738, 360582318685255947]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360568434031456543, 360568457221706501⟩, ⟨835519921600022787, 836465245045125795⟩, true⟩

def words03 : List Nat := [360582319200828689, 360582319716546246, 360582319989617539, 360582320074213022, 360582320074924310, 360582319983276482, 360582320073565722, 360582320074410204, 360582319983624786, 360582319754769894]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360612620249866166, 360612643448086241⟩, ⟨(-1830872746792269051), (-1829926942392594533)⟩, true⟩

def words04 : List Nat := [360582319525716031, 360582319637156629, 360582320043253448, 360582320449500558, 360582320612674253, 360582320873631885, 360582321047717390, 360582321222033141, 360582321542612118, 360582322045915729]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk603A
