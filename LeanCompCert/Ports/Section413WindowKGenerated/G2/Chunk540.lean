import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk540

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

def state06 : KState := ⟨⟨360585774364372943, 360585792815203657⟩, ⟨(-212360248925190983), (-211686311875003553)⟩, true⟩

def words05 : List Nat := [360581876889664993, 360581876660598437, 360581876480045453, 360581876852526929, 360581877055774387, 360581877259136118, 360581877259805117, 360581877244377724, 360581877048309866, 360581877121600598]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360553703598846229, 360553722056750247⟩, ⟨1521470976872771850, 1522145296342491108⟩, true⟩

def words06 : List Nat := [360581877186704233, 360581877187454872, 360581876911073958, 360581876462936491, 360581876014696820, 360581875342986225, 360581874843155063, 360581874445708651, 360581874048182154, 360581873440074503]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360578078439085715, 360578096904077115⟩, ⟨203385676581465172, 204060379301363744⟩, true⟩

def words07 : List Nat := [360581872920044191, 360581872673161571, 360581872426061211, 360581872338472272, 360581872109623100, 360581871552068965, 360581870994388323, 360581870550803253, 360581870278900479, 360581870209907392]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360561209856521403, 360561228328673147⟩, ⟨1115693079040506796, 1116368169027917256⟩, true⟩

def words08 : List Nat := [360581870140811761, 360581869897555268, 360581869769369320, 360581869876396333, 360581869877025331, 360581869824682409, 360581869431107239, 360581868761599432, 360581868091983168, 360581867414807884]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360562829752027083, 360562848231254341⟩, ⟨1028136889086125181, 1028812361822995175⟩, true⟩

def words09 : List Nat := [360581867033852777, 360581866994158125, 360581866954387710, 360581866678013818, 360581866470018149, 360581866111657270, 360581865753073959, 360581865625622754, 360581865446354686, 360581865095613362]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk540
