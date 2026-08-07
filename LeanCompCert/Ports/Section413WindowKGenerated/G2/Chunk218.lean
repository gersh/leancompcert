import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk218

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586361793817030, 360586364573381337⟩, ⟨(-139110488948777839), (-139069489144890513)⟩, true⟩

def state01 : KState := ⟨⟨360566299702247353, 360566302484489722⟩, ⟨298050402231671010, 298091460430630812⟩, true⟩

def words00 : List Nat := [360579985531885481, 360579984408982124, 360579983705156944, 360579984401697980, 360579984401937759, 360579983535056171, 360579980575661023, 360579976566725312, 360579972558103260, 360579970135128449]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360487785814641256, 360487788599539780⟩, ⟨2010995141573957829, 2011036257717099323⟩, true⟩

def words01 : List Nat := [360579969562273418, 360579969616112351, 360579969616364815, 360579968098378714, 360579966011752014, 360579963393883937, 360579960776170690, 360579960252367924, 360579957638054746, 360579953414283919]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598559287393699, 360598562074951367⟩, ⟨(-406566796264640494), (-406525622085972738)⟩, true⟩

def words02 : List Nat := [360579949190836800, 360579947061026844, 360579946419375939, 360579946854509177, 360579946854771479, 360579945356125797, 360579943927985280, 360579942030770205, 360579940133646093, 360579940590727742]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360549863879145378, 360549866669391200⟩, ⟨656566403299171103, 656607636173615115⟩, true⟩

def words03 : List Nat := [360579940590979327, 360579940148550010, 360579939706111347, 360579939764867501, 360579939765105096, 360579938943644453, 360579938122228396, 360579935964593845, 360579932497909446, 360579931121596952]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360558545126135161, 360558547919035627⟩, ⟨466880879586032565, 466922170451263529⟩, true⟩

def words04 : List Nat := [360579930458686249, 360579930458968376, 360579929917215254, 360579928286861308, 360579926656611248, 360579923738902634, 360579922455057167, 360579921105870789, 360579919756777076, 360579917354754221]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360646586748984831, 360646589544547531⟩, ⟨(-1457343655745451609), (-1457302306696997971)⟩, true⟩

def words05 : List Nat := [360579917487031445, 360579918597253549, 360579919741286712, 360579921115555793, 360579921115816123, 360579920742538698, 360579920369243113, 360579921246909217, 360579924296922577, 360579927346720488]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360659845938064571, 360659848736322673⟩, ⟨(-1747568600116882757), (-1747527192133922389)⟩, true⟩

def words06 : List Nat := [360579928723310501, 360579929446972345, 360579932256198392, 360579935065249737, 360579937344018380, 360579939657133894, 360579940647168020, 360579941637149058, 360579943514592598, 360579947168395559]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360545557004596215, 360545559805512605⟩, ⟨752816579350459610, 752858045483610048⟩, true⟩

def words07 : List Nat := [360579952905917098, 360579958642967892, 360579963046587477, 360579965371060908, 360579966271611311, 360579967172149481, 360579969565669318, 360579969880628241, 360579969880885747, 360579968308505458]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360636968859959247, 360636971663545817⟩, ⟨(-1247495166805991054), (-1247453642235950230)⟩, true⟩

def words08 : List Nat := [360579967246204002, 360579969386816297, 360579972999896977, 360579976612701357, 360579978437064346, 360579979116160042, 360579981077252725, 360579983038251976, 360579984288092205, 360579986891619640]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360627890479328898, 360627893285606087⟩, ⟨(-1048632274630007035), (-1048590691149062347)⟩, true⟩

def words09 : List Nat := [360579988445257249, 360579989998785123, 360579993632171795, 360579998634191730, 360580002595321509, 360580006556141307, 360580009438471514, 360580010245137427, 360580012431806557, 360580014618369474]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk218
