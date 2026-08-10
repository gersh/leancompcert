import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk944A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360594081454952484, 360594140248892799⟩, ⟨(-1140997390314332889), (-1137249614915718135)⟩, true⟩

def state01 : KState := ⟨⟨360595836042881114, 360595894849871869⟩, ⟨(-1306668336286833707), (-1302919328861713927)⟩, true⟩

def words00 : List Nat := [360582093290697877, 360582093401041171, 360582093589902837, 360582093779162101, 360582093923964737, 360582094035667916, 360582094090868557, 360582094146217377, 360582094198695728, 360582094346446827]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 94400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 94400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574636674152592, 360574695494022923⟩, ⟨694881618695285500, 698631842146361346⟩, true⟩

def words01 : List Nat := [360582094543054702, 360582094739918253, 360582094852584570, 360582094853952277, 360582094854727414, 360582094795511990, 360582094767968959, 360582094769340462, 360582094764386431, 360582094687436886]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 94410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 94400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598087366769909, 360598146199567723⟩, ⟨(-1519491966924906484), (-1515740522799601678)⟩, true⟩

def words02 : List Nat := [360582094643929024, 360582094735046741, 360582094780257236, 360582094825719778, 360582094826982642, 360582094776409003, 360582094658391767, 360582094652894624, 360582094725892417, 360582094897317407]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 94420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 94400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595946795687690, 360596005641503288⟩, ⟨(-1317354514780325281), (-1313601841319657853)⟩, true⟩

def words03 : List Nat := [360582095012199940, 360582095127236006, 360582095354085580, 360582095637158561, 360582095811954460, 360582095986959022, 360582096075031016, 360582096111614868, 360582096260004881, 360582096408846713]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 94430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 94400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599998478482386, 360600057337180197⟩, ⟨(-1700034516747301533), (-1696280626626484533)⟩, true⟩

def words04 : List Nat := [360582096669299306, 360582096818285932, 360582096910828739, 360582097003542869, 360582097034150200, 360582097152065268, 360582097381606589, 360582097611405392, 360582097773807403, 360582097965372313]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 94440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 94400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk944A
