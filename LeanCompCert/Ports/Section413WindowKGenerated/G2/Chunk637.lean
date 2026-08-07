import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk637

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590883012672664, 360590908968999014⟩, ⟨(-524344407870498551), (-523227486888953773)⟩, true⟩

def state01 : KState := ⟨⟨360612070420963443, 360612096385736444⟩, ⟨(-1874108678955485126), (-1872991219879643868)⟩, true⟩

def words00 : List Nat := [360582695332908421, 360582695624958325, 360582696162976967, 360582696701150200, 360582697027822481, 360582697191424322, 360582697273514663, 360582697355850936, 360582697684134800, 360582698146501781]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 63700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 63700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605403633689856, 360605429607003807⟩, ⟨(-1449348984833109427), (-1448230981572733733)⟩, true⟩

def words01 : List Nat := [360582698486159628, 360582698825903147, 360582699161398049, 360582699727919119, 360582700232017338, 360582700736248324, 360582701092825520, 360582701204274313, 360582701561690608, 360582701919403601]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 63710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 63700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598055686607369, 360598081668369809⟩, ⟨(-981184936172182128), (-980066394532198104)⟩, true⟩

def words02 : List Nat := [360582702270375451, 360582702436232570, 360582702437036291, 360582702415804628, 360582702394428269, 360582702398705433, 360582702734963266, 360582703071397747, 360582703252338961, 360582703494568485]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 63720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 63700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360617701507675753, 360617727497896055⟩, ⟨(-2233346448692674930), (-2232227367990545356)⟩, true⟩

def words03 : List Nat := [360582703919428024, 360582704344537429, 360582704727519701, 360582705072211839, 360582705180575730, 360582705288992474, 360582705643246134, 360582706122073685, 360582706672242978, 360582707222594593]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 63730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 63700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360609081474949137, 360609107473714790⟩, ⟨(-1683887186659881062), (-1682767561235751018)⟩, true⟩

def words04 : List Nat := [360582707649037552, 360582708168353926, 360582708933427055, 360582709698739205, 360582710255819690, 360582710568046531, 360582710754496217, 360582710941029639, 360582711118786731, 360582711533867012]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 63740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 63700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360582165609452530, 360582191616662428⟩, ⟨32184845136612697, 33305008921605093⟩, true⟩

def words05 : List Nat := [360582712091970824, 360582712650232688, 360582713068757116, 360582713305321355, 360582713421114677, 360582713537176293, 360582713840485466, 360582713972703042, 360582713973502141, 360582713966237736]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590618311721214, 360590644327406522⟩, ⟨(-506781242470892862), (-505660538251605152)⟩, true⟩

def words06 : List Nat := [360582714196405344, 360582714557551391, 360582714912033046, 360582715266664591, 360582715422422066, 360582715423318859, 360582715334169951, 360582715132861692, 360582714931297055, 360582715009405368]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360594792911481390, 360594818935705018⟩, ⟨(-773011012675508437), (-771889763925093027)⟩, true⟩

def words07 : List Nat := [360582715010205102, 360582714984283845, 360582715177108500, 360582715522014413, 360582715802898470, 360582716083919158, 360582716176362624, 360582716364709734, 360582716555191318, 360582716745963166]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593395248152340, 360593421280816877⟩, ⟨(-683870285558017685), (-682748498402683855)⟩, true⟩

def words08 : List Nat := [360582717182123095, 360582717373728755, 360582717410529828, 360582717447436612, 360582717448187323, 360582717519480615, 360582717813473764, 360582718107629934, 360582718215169710, 360582718383881531]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617613369143115, 360617639410289010⟩, ⟨(-2228995324077014857), (-2227872995855076709)⟩, true⟩

def words09 : List Nat := [360582718451645804, 360582718519664144, 360582718833012488, 360582718961645826, 360582718962473167, 360582718883409780, 360582718919063408, 360582719221854917, 360582719769918748, 360582720318176738]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk637
