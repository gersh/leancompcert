import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk934A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk934A
