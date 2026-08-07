import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk934

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584059968290045, 360584117475639239⟩, ⟨(-196368902125654805), (-192741938729450859)⟩, true⟩

def state01 : KState := ⟨⟨360583856231924509, 360583913752054438⟩, ⟨(-177392397753437615), (-173764240572632131)⟩, true⟩

def words00 : List Nat := [360582053880665125, 360582053864845943, 360582053892293434, 360582053920000005, 360582053921252782, 360582053851482220, 360582053667115254, 360582053597752764, 360582053527969625, 360582053540295945]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 93400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 93400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583365495685420, 360583423028697480⟩, ⟨(-131578205177362369), (-127948844612861569)⟩, true⟩

def words01 : List Nat := [360582053541511916, 360582053490821810, 360582053480916762, 360582053580663019, 360582053581817480, 360582053574648524, 360582053567332145, 360582053502569681, 360582053418440391, 360582053434659600]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 93410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 93400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360588415225299019, 360588472771057389⟩, ⟨(-603343432181932761), (-599712880792458803)⟩, true⟩

def words02 : List Nat := [360582053538297735, 360582053645099182, 360582053652787186, 360582053660611876, 360582053661745613, 360582053620649696, 360582053750954447, 360582053881515681, 360582053922597554, 360582053992699109]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 93420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 93400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609316471230447, 360609374029756029⟩, ⟨(-2556260544115435000), (-2552628799823878072)⟩, true⟩

def words03 : List Nat := [360582054096551775, 360582054200798345, 360582054400305974, 360582054620005350, 360582054742351066, 360582054864823628, 360582055077444317, 360582055361609448, 360582055655069790, 360582055948829842]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 93430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 93400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584654348035646, 360584711919465032⟩, ⟨(-251769836733534867), (-248136886648488821)⟩, true⟩

def words04 : List Nat := [360582056184831594, 360582056370487301, 360582056552093980, 360582056734081771, 360582056842173191, 360582056843525893, 360582056837464587, 360582056773075048, 360582056708432222, 360582056657491929]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 93440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 93400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360556176492378958, 360556234076537006⟩, ⟨2409696222236764539, 2413330361880435643⟩, true⟩

def words05 : List Nat := [360582056780589094, 360582056903943155, 360582056969611016, 360582056970963816, 360582056922343629, 360582056845267623, 360582056767796061, 360582056635789198, 360582056418216112, 360582056143323658]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 93450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 93400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578405438454250, 360578463035381257⟩, ⟨332071048216615069, 335706381310218983⟩, true⟩

def words06 : List Nat := [360582055868132494, 360582055643310782, 360582055493348400, 360582055458095780, 360582055422727992, 360582055289199398, 360582055116534338, 360582054923809601, 360582054730691638, 360582054630345526]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 93460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 93400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593068293878695, 360593125903707130⟩, ⟨(-1038599184731714136), (-1034962645678096880)⟩, true⟩

def words07 : List Nat := [360582054593147205, 360582054468041105, 360582054342676349, 360582054342904784, 360582054344255494, 360582054345825653, 360582054347031053, 360582054295189783, 360582054414721755, 360582054534705108]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 93470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 93400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360592180305618937, 360592237928179407⟩, ⟨(-955588717424150364), (-951950988114130216)⟩, true⟩

def words08 : List Nat := [360582054768613504, 360582054930381201, 360582055004913600, 360582055079571267, 360582055080723398, 360582055128192544, 360582055295201351, 360582055462466022, 360582055543763008, 360582055654076936]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 93480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 93400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603365551809306, 360603423187173001⟩, ⟨(-2001316338017031007), (-1997677411673735141)⟩, true⟩

def words09 : List Nat := [360582055878446817, 360582056103250479, 360582056441973747, 360582056666839119, 360582056784215106, 360582056901700766, 360582057133269949, 360582057422315228, 360582057651942162, 360582057881864248]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 93490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 93400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 93400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk934
