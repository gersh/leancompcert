import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk218A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk218B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk218A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk218B
