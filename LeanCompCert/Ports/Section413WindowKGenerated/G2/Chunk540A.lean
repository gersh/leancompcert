import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk540A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360555942603672119, 360555961011919055⟩, ⟨1398941435275861479, 1399613071526456799⟩, true⟩

def state01 : KState := ⟨⟨360574110037188813, 360574128452493104⟩, ⟨417825864412518264, 418497881795535076⟩, true⟩

def words00 : List Nat := [360581879293140863, 360581879156206058, 360581879063498668, 360581878770831463, 360581878478062633, 360581877948132720, 360581877590476337, 360581877467962851, 360581877345379766, 360581876978354899]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598382671514371, 360598401093901692⟩, ⟨(-893206380311253510), (-892533980338093124)⟩, true⟩

def words01 : List Nat := [360581877034196202, 360581877233726295, 360581877775155949, 360581878057612230, 360581878058306948, 360581878050106091, 360581878184245259, 360581878498969788, 360581878805447398, 360581879112073550]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598793103597122, 360598811533125994⟩, ⟨(-915575675398995023), (-914902889604233889)⟩, true⟩

def words02 : List Nat := [360581879161735213, 360581879162485296, 360581878870027169, 360581878831820623, 360581878793417593, 360581878702214695, 360581878702891345, 360581878486381750, 360581878293521728, 360581878607775654]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360570315563990924, 360570334000592456⟩, ⟨623246669322038400, 623919837287542214⟩, true⟩

def words03 : List Nat := [360581879166161457, 360581879724675249, 360581880026756969, 360581880027507257, 360581879987563363, 360581879802549188, 360581879773268856, 360581879774019531, 360581879732278655, 360581879519417170]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580682919774360, 360580701363454021⟩, ⟨62864780577617124, 63538331080487160⟩, true⟩

def words04 : List Nat := [360581879306383064, 360581879256627629, 360581879257240086, 360581879219938453, 360581879182585962, 360581878853209511, 360581878290981696, 360581877717093279, 360581877143006083, 360581876910745057]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk540A
