import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk274A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360517485155868120, 360517489636233638⟩, ⟨1794006670913186007, 1794089705906676681⟩, true⟩

def state01 : KState := ⟨⟨360576326799282399, 360576331283051417⟩, ⟨181285155437884443, 181368283703759271⟩, true⟩

def words00 : List Nat := [360582964973409668, 360582962312081780, 360582960319066016, 360582959230036225, 360582958141064194, 360582955768642725, 360582952535900649, 360582950630918513, 360582948725970088, 360582948148564141]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 27400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 27400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360526119651362274, 360526124138571434⟩, ⟨1557880992950149722, 1557964215527338810⟩, true⟩

def words01 : List Nat := [360582947907491049, 360582946997606878, 360582946102545317, 360582946793132680, 360582947144368774, 360582947495638539, 360582947495962411, 360582946782149300, 360582944744875616, 360582942673054561]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 27410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 27400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360525671288370352, 360525675778978142⟩, ⟨1569953391148450190, 1570036706933446016⟩, true⟩

def words02 : List Nat := [360582940601266367, 360582938975484303, 360582936026529887, 360582932061397603, 360582928096496073, 360582923791169730, 360582920502956777, 360582918540242213, 360582916577631599, 360582913719442359]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 27420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 27400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360620817732159081, 360620822226181063⟩, ⟨(-1040449640557911500), (-1040366231105209274)⟩, true⟩

def words03 : List Nat := [360582911633119351, 360582910872028667, 360582910110889076, 360582909315623903, 360582908999909321, 360582907506724054, 360582906013577942, 360582906622493956, 360582908004550624, 360582909386594124]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 27430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 27400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360557089344770444, 360557093842233417⟩, ⟨708200645289223214, 708284149179742686⟩, true⟩

def words04 : List Nat := [360582910101868739, 360582910102230033, 360582909495318810, 360582909272527739, 360582909049659587, 360582907954143628, 360582905536762964, 360582902097675947, 360582898658770391, 360582896543478581]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 27440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 27400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk274A
