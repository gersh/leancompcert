import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk590A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk590B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk590A

def state06 : KState := ⟨⟨360586083089334272, 360586105268318503⟩, ⟨(-242854296767850884), (-241969348329208250)⟩, true⟩

def words05 : List Nat := [360582007212857594, 360582007360630807, 360582007795024278, 360582007943777160, 360582007944538384, 360582007851121569, 360582007872619228, 360582008188460657, 360582008258518698, 360582008328741977]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 59050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 59000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598537202042843, 360598559388877222⟩, ⟨(-978641029039955505), (-977755616931874375)⟩, true⟩

def words06 : List Nat := [360582008329477017, 360582008255250358, 360582007895141934, 360582007822057664, 360582007748755760, 360582007602013938, 360582007462000722, 360582007178540552, 360582006897377273, 360582007178538277]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 59060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 59000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360556673986092984, 360556696180709367⟩, ⟨1494453787192252207, 1495339659021635727⟩, true⟩

def words07 : List Nat := [360582007583494775, 360582007988598453, 360582008128312613, 360582008129138116, 360582007983190876, 360582007656310759, 360582007329190130, 360582007288867417, 360582007029025392, 360582006601478183]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 59070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 59000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360568249786648118, 360568271989051857⟩, ⟨810489262996679473, 811375594941410385⟩, true⟩

def words08 : List Nat := [360582006173748277, 360582005687724028, 360582005381832543, 360582005362705430, 360582005343525266, 360582005068221022, 360582004624949213, 360582004085738538, 360582003546304103, 360582003171907525]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 59080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 59000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583752108708410, 360583774318976200⟩, ⟨(-105629530444586766), (-104742733775799568)⟩, true⟩

def words09 : List Nat := [360582002940269480, 360582002564430310, 360582002188437661, 360582002252317733, 360582002279654838, 360582002307125937, 360582002307861477, 360582002191073467, 360582002021353504, 360582002052283999]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 59090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 59000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 59000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk590B
