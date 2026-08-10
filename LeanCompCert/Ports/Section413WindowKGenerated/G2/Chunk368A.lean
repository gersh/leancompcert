import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk368A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360636547217602541, 360636555502713850⟩, ⟨(-2021054691929511107), (-2020848586895608863)⟩, true⟩

def state01 : KState := ⟨⟨360621562786485404, 360621571076318148⟩, ⟨(-1469928123614435095), (-1469721844808502593)⟩, true⟩

def words00 : List Nat := [360581643637190929, 360581643906358925, 360581644033712086, 360581644161200754, 360581644161616426, 360581643935831815, 360581643936273146, 360581643655992291, 360581643831933772, 360581644917158970]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 36800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 36800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360565741732638342, 360565750027142376⟩, ⟨585239198876346664, 585445649656184562⟩, true⟩

def words01 : List Nat := [360581646570087646, 360581648223021431, 360581649313438165, 360581649899092675, 360581650140301670, 360581650381631215, 360581650729853873, 360581650730349791, 360581650666226677, 360581650234900556]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 36810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 36800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596818526904899, 360596826826088356⟩, ⟨(-559039676194644674), (-558833053095802128)⟩, true⟩

def words02 : List Nat := [360581650108266269, 360581650975628660, 360581652183878988, 360581653392158075, 360581653974914149, 360581653975409902, 360581653822177133, 360581653647092668, 360581653514331392, 360581653926816118]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 36820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 36800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577709829795699, 360577718133695684⟩, ⟨144970470037744459, 145177266870367857⟩, true⟩

def words03 : List Nat := [360581653967968870, 360581654009173648, 360581654786291246, 360581656132056917, 360581657161366370, 360581658190700846, 360581658853275419, 360581658990698794, 360581658991103529, 360581658884696509]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 36830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 36800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590357041958095, 360590365350535826⟩, ⟨(-321204338658664935), (-320997369475245277)⟩, true⟩

def words04 : List Nat := [360581658778138855, 360581658416404001, 360581657895099435, 360581657002806626, 360581656110481193, 360581655030541336, 360581654580312742, 360581654723274913, 360581654723716826, 360581654667800616]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 36840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 36800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk368A
