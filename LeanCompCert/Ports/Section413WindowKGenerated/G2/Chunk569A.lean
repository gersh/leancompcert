import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk569A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360617528638979370, 360617549163982341⟩, ⟨(-2032311191931178791), (-2031522153050049949)⟩, true⟩

def state01 : KState := ⟨⟨360596001373638634, 360596021906201079⟩, ⟨(-807515713278876025), (-806726244226199655)⟩, true⟩

def words00 : List Nat := [360581846845797165, 360581847135501654, 360581847263901380, 360581847392513653, 360581847393178632, 360581847370704710, 360581847174387120, 360581846824035371, 360581846473543795, 360581846680950667]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 56900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 56900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578763115324706, 360578783655352926⟩, ⟨173735818870244403, 174525712837128231⟩, true⟩

def words01 : List Nat := [360581847239179570, 360581847797540759, 360581848171263746, 360581848645949461, 360581849041887945, 360581849438034666, 360581849763510353, 360581849865684994, 360581849866391587, 360581849813343740]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 56910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 56900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360608385356499412, 360608405904012773⟩, ⟨(-1512446036667297125), (-1511655716609640603)⟩, true⟩

def words02 : List Nat := [360581850014670675, 360581850448575646, 360581851190639245, 360581851932844236, 360581852354417206, 360581852468558813, 360581852549064815, 360581852629797112, 360581853018656156, 360581853485881885]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 56920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 56900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360606495893374337, 360606516448453346⟩, ⟨(-1404942903721130380), (-1404152152913774764)⟩, true⟩

def words03 : List Nat := [360581853716446551, 360581853947077836, 360581854263978567, 360581854738617524, 360581855074377135, 360581855410259651, 360581855590855756, 360581855807395276, 360581856241135489, 360581856675128084]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 56930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 56900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594427721499291, 360594448284045618⟩, ⟨(-717731896409509614), (-716940720376037806)⟩, true⟩

def words04 : List Nat := [360581857417078076, 360581857945905170, 360581858252249499, 360581858558660518, 360581858656434347, 360581858908055450, 360581859112690368, 360581859317466412, 360581859332907082, 360581859554780530]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 56940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 56900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk569A
