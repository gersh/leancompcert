import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk779A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360617236905262080, 360617276349245460⟩, ⟨(-2733219453406565658), (-2731144162629867640)⟩, true⟩

def state01 : KState := ⟨⟨360597055331383875, 360597094785974270⟩, ⟨(-1161067368556651293), (-1158991251441700519)⟩, true⟩

def words00 : List Nat := [360582217530202155, 360582217853506626, 360582218135100031, 360582218417007700, 360582218657328715, 360582218733450158, 360582218734441329, 360582218728197653, 360582218757838428, 360582218950066097]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 77900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 77900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360557868795656491, 360557908260710482⟩, ⟨1892209695211944941, 1894286627599862685⟩, true⟩

def words01 : List Nat := [360582219197677267, 360582219445492606, 360582219568098860, 360582219569211222, 360582219569000826, 360582219527850151, 360582219486389335, 360582219441197229, 360582219231563181, 360582218920715614]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 77910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 77900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590321941994747, 360590361417555304⟩, ⟨(-636702357383728028), (-634624606274393326)⟩, true⟩

def words02 : List Nat := [360582218609624108, 360582218416132703, 360582218363536105, 360582218382462281, 360582218383489703, 360582218263301058, 360582218033205880, 360582217932910630, 360582217895214453, 360582218000862661]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 77920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 77900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596315515088446, 360596355001268145⟩, ⟨(-1103852605593020224), (-1101774026882208238)⟩, true⟩

def words03 : List Nat := [360582218001880773, 360582217981040666, 360582218102469574, 360582218340974773, 360582218445554301, 360582218550301724, 360582218565172130, 360582218635689019, 360582218817963854, 360582219000615316]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 77930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 77900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585552365098858, 360585591861755599⟩, ⟨(-264953317344931032), (-262873922000184700)⟩, true⟩

def words04 : List Nat := [360582219280851688, 360582219397064292, 360582219430890639, 360582219464837310, 360582219465787633, 360582219352749771, 360582219435710616, 360582219518886412, 360582219520358427, 360582219564774160]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 77940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 77900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk779A
