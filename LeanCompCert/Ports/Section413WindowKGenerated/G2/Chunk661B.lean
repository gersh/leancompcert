import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk661A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk661B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk661A

def state06 : KState := ⟨⟨360553857776117343, 360553885861021547⟩, ⟨1921339770109737339, 1922594917337011837⟩, true⟩

def words05 : List Nat := [360582946953011225, 360582946987376610, 360582946988207648, 360582946908261182, 360582946881301784, 360582946753251652, 360582946624948080, 360582946400944986, 360582946077370969, 360582945639094961]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360593951035772607, 360593979129480437⟩, ⟨(-731434520003719800), (-730178790284295906)⟩, true⟩

def words06 : List Nat := [360582945200620962, 360582944990521611, 360582944980978088, 360582945068167022, 360582945069033189, 360582944932547506, 360582944567943638, 360582944381960413, 360582944236712031, 360582944404445539]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360613076599823925, 360613104702427707⟩, ⟨(-1997137144500079614), (-1995880826092457062)⟩, true⟩

def words07 : List Nat := [360582944405292611, 360582944383833216, 360582944567801440, 360582944920554225, 360582945213017437, 360582945505629627, 360582945647715031, 360582945876418672, 360582946332882193, 360582946789641674]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585961247387443, 360585989358773500⟩, ⟨(-202556965061472097), (-201300065397531721)⟩, true⟩

def words08 : List Nat := [360582947303683153, 360582947590005973, 360582947732806588, 360582947875700661, 360582947876496087, 360582947917119385, 360582948020037002, 360582948123125048, 360582948123956649, 360582948158830947]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360613922716996955, 360613950837211076⟩, ⟨(-2053455481664491609), (-2052197997629606835)⟩, true⟩

def words09 : List Nat := [360582948433412280, 360582948708276973, 360582949116205338, 360582949421839547, 360582949531910005, 360582949642048238, 360582949909680301, 360582950397438444, 360582950866491105, 360582951335728779]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk661B
