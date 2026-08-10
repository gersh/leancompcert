import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk835A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488092087213092, 362488196981875419⟩, ⟨(-246255867686608886), (-240341750617975622)⟩, true⟩

def state01 : KState := ⟨⟨362491499445411599, 362491604366023132⟩, ⟨(-530789414731604493), (-524873130770113687)⟩, true⟩

def words00 : List Nat := [371285318782232119, 371285318822172596, 371285318909384381, 371285318997785472, 371285319074074052, 371285319076971751, 371285319026976105, 371285319071225080, 371285319209927262, 371285319288239725]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 83500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 83500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488299615123585, 362488404562182437⟩, ⟨(-263529835662056338), (-257611342961248234)⟩, true⟩

def words01 : List Nat := [371285319365448934, 371285319443675178, 371285319623281434, 371285319741831541, 371285319903142689, 371285320065533757, 371285320174263573, 371285320177160706, 371285320131512068, 371285320172113338]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 83510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 83500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476443310032657, 362476548282880016⟩, ⟨726767621776511523, 732688268469578055⟩, true⟩

def words02 : List Nat := [371285320302250875, 371285320305148061, 371285320244445656, 371285320157015320, 371285320068454257, 371285320007291966, 371285319873327607, 371285319863033273, 371285319851754235, 371285319841223960]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 83520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 83500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499264074973678, 362499369074034825⟩, ⟨(-1179596110839920519), (-1173673274377624849)⟩, true⟩

def words03 : List Nat := [371285319738213677, 371285319695713537, 371285319731832794, 371285319734750103, 371285319688471345, 371285319620017657, 371285319621986450, 371285319663481215, 371285319833622186, 371285320005022273]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 83530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 83500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480276525027737, 362480381550186220⟩, ⟨406691844795984259, 412616861564763303⟩, true⟩

def words04 : List Nat := [371285320175203760, 371285320178101572, 371285320239825449, 371285320326011664, 371285320400377025, 371285320403276456, 371285320312196737, 371285320222027913, 371285320130710668, 371285320112263596]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 83540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 83500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk835A
