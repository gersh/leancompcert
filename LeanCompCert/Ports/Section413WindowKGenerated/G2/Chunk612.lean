import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk612

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592107481352751, 360592131364082452⟩, ⟨(-590346812985423950), (-589359406827757680)⟩, true⟩

def state01 : KState := ⟨⟨360582767749484892, 360582791640296094⟩, ⟨(-18785945015428566), (-17798044229111026)⟩, true⟩

def words00 : List Nat := [360582501614502460, 360582501615359965, 360582501581037926, 360582501378353809, 360582501175526355, 360582500904641545, 360582500857694609, 360582500931176719, 360582500931948232, 360582500874841697]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595746361979575, 360595770260883558⟩, ⟨(-813258533824353527), (-812270137639692755)⟩, true⟩

def words01 : List Nat := [360582501147035012, 360582501419471154, 360582501848952555, 360582502079947173, 360582502080757104, 360582502043559853, 360582502006204609, 360582501990665531, 360582502208090447, 360582502425702172]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360605105409041778, 360605129316122620⟩, ⟨(-1386322114485763488), (-1385333217673066242)⟩, true⟩

def words02 : List Nat := [360582502509241473, 360582502599292131, 360582502955803236, 360582503312554478, 360582503539539720, 360582503817224439, 360582503961302753, 360582504105463052, 360582504242174259, 360582504612660762]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574834434754808, 360574858349911965⟩, ⟨467444152903622861, 468433544269006215⟩, true⟩

def words03 : List Nat := [360582505249419810, 360582505886322976, 360582506389221310, 360582506802847323, 360582507083931525, 360582507365260006, 360582507582572901, 360582507616605982, 360582507617370245, 360582507493352021]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593480043311208, 360593503966578346⟩, ⟨(-674542206135997632), (-673552318075976532)⟩, true⟩

def words04 : List Nat := [360582507425503555, 360582507648139960, 360582507762554048, 360582507877113693, 360582507877912194, 360582507763546139, 360582507443281825, 360582507319364339, 360582507195192847, 360582507373574543]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360581780349833459, 360581804281270758⟩, ⟨42172897184059674, 43163285706860250⟩, true⟩

def words05 : List Nat := [360582507374341007, 360582507368755291, 360582507622955315, 360582508052807368, 360582508414240472, 360582508775808550, 360582508933933763, 360582508934792193, 360582508883463761, 360582508872940802]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 61250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 61200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591653157860024, 360591677097377131⟩, ⟨(-562734109497013017), (-561743225963859025)⟩, true⟩

def words06 : List Nat := [360582509116955376, 360582509117813794, 360582509108121453, 360582508963642058, 360582508819012289, 360582508606507145, 360582508663722722, 360582508802047832, 360582508802816074, 360582508922776360]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 61260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 61200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360607664686789059, 360607688634414339⟩, ⟨(-1543943973101306580), (-1542952592741044646)⟩, true⟩

def words07 : List Nat := [360582509065793101, 360582509209055744, 360582509542070087, 360582509610045779, 360582509610840193, 360582509457421855, 360582509303844568, 360582509491645464, 360582509903226279, 360582510314988399]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 61270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 61200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593594239619318, 360593618195424580⟩, ⟨(-681759044312946576), (-680767162643399058)⟩, true⟩

def words08 : List Nat := [360582510524096452, 360582510655456509, 360582511052741429, 360582511450265442, 360582511593815099, 360582511594673876, 360582511473150197, 360582511206062650, 360582510938818942, 360582511064481320]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 61280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 61200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360567703816864140, 360567727780768140⟩, ⟨905301932622032732, 906294310703365850⟩, true⟩

def words09 : List Nat := [360582511512420989, 360582511960531505, 360582512274858442, 360582512472778453, 360582512473501880, 360582512436973559, 360582512628694721, 360582512629553709, 360582512593834232, 360582512353536548]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 61290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 61200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 61200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk612
