import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk691A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360539863979662648, 360539894722140102⟩, ⟨2961106704226530104, 2962541613510947878⟩, true⟩

def state01 : KState := ⟨⟨360567563235485217, 360567593987193502⟩, ⟨1046952437956010403, 1048387985136241443⟩, true⟩

def words00 : List Nat := [360582767353044973, 360582766868276695, 360582766547015822, 360582766318539470, 360582766089979417, 360582765659428550, 360582765064695456, 360582764584322271, 360582764103671220, 360582763832152788]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 69100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 69100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561056646522374, 360561087407559010⟩, ⟨1496568243693008826, 1498004435603399750⟩, true⟩

def words01 : List Nat := [360582763613547827, 360582763235723082, 360582762857727512, 360582762443406104, 360582762134184569, 360582761710798736, 360582761287318247, 360582760759488811, 360582760237862195, 360582759925435217]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 69110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 69100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360572501002422269, 360572531772665729⟩, ⟨705441153032326610, 706877981364178338⟩, true⟩

def words02 : List Nat := [360582759612685185, 360582759353741902, 360582759128942486, 360582758799809723, 360582758470535972, 360582757991555374, 360582757642204827, 360582757501853331, 360582757361407581, 360582757115951773]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 69120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 69100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589044470927701, 360589075250419757⟩, ⟨(-438251762263959573), (-436814294531588971)⟩, true⟩

def words03 : List Nat := [360582756976074207, 360582756984414433, 360582757160567510, 360582757277309173, 360582757278217452, 360582757187083916, 360582757144808756, 360582757334043353, 360582757426229199, 360582757518617620]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 69130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 69100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604979273686262, 360605010062491910⟩, ⟨(-1540213244566685722), (-1538775132846767870)⟩, true⟩

def words04 : List Nat := [360582757519491170, 360582757483086928, 360582757293704425, 360582757304045822, 360582757304864700, 360582757328558042, 360582757329442940, 360582757266448076, 360582757347956997, 360582757670872892]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 69140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 69100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk691A
