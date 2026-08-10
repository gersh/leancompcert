import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk908A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580489959083958, 360580544189622175⟩, ⟨129442100106701484, 132767247875750668⟩, true⟩

def state01 : KState := ⟨⟨360567110887337263, 360567165130374300⟩, ⟨1344237633274184326, 1347563915995811170⟩, true⟩

def words00 : List Nat := [360582006369061896, 360582006270217676, 360582006080999060, 360582006013329544, 360582005945298752, 360582005773848498, 360582005481161017, 360582005127870216, 360582004774335970, 360582004508372272]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561001590158544, 360561055845563973⟩, ⟨1899026172842229905, 1902353578799272579⟩, true⟩

def words01 : List Nat := [360582004346041350, 360582004181258629, 360582004016336300, 360582003790831178, 360582003525062192, 360582003202626172, 360582002879801676, 360582002660608155, 360582002491697722, 360582002262419284]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576841282389344, 360576895550165978⟩, ⟨460430105498974484, 463758635069690168⟩, true⟩

def words02 : List Nat := [360582002032845355, 360582001924737062, 360582001949512189, 360582002023216493, 360582002024448665, 360582001983933316, 360582001822130986, 360582001632075773, 360582001441623444, 360582001337186453]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360568902404996335, 360568956685279618⟩, ⟨1181580960097462102, 1184910625710232930⟩, true⟩

def words03 : List Nat := [360582001282151916, 360582001133915611, 360582000985408260, 360582000990666086, 360582000991764434, 360582000968228174, 360582000944560286, 360582000860523775, 360582000757646697, 360582000615549436]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581894436968361, 360581948729609582⟩, ⟨1298288166504401, 4629076434136019⟩, true⟩

def words04 : List Nat := [360582000473019072, 360582000451775971, 360582000348501588, 360582000181169655, 360582000013621092, 360581999816061344, 360581999732968209, 360581999752717065, 360581999753893861, 360581999682569782]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk908A
