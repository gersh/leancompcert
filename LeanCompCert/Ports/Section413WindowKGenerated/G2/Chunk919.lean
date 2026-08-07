import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk919

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360568861062734271, 360568916667443039⟩, ⟨1195990339687642583, 1199441019473461079⟩, true⟩

def state01 : KState := ⟨⟨360586013567753242, 360586069185028958⟩, ⟨(-380469193283758318), (-377017358536495142)⟩, true⟩

def words00 : List Nat := [360581968115395213, 360581968047349763, 360581968048444799, 360581968019010300, 360581967989481504, 360581967840817169, 360581967573773755, 360581967395735652, 360581967217293042, 360581967202039583]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 91900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 91900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574233562689176, 360574289192605468⟩, ⟨702324636178208334, 705777632785769818⟩, true⟩

def words01 : List Nat := [360581967203223402, 360581967189761974, 360581967255647906, 360581967395909584, 360581967484094983, 360581967572503570, 360581967573719429, 360581967569683766, 360581967447301624, 360581967365285906]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 91910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 91900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580098880326676, 360580154522756569⟩, ⟨163181222686740649, 166635369606814561⟩, true⟩

def words02 : List Nat := [360581967317491018, 360581967365363347, 360581967366552966, 360581967339585507, 360581967312379275, 360581967256145726, 360581967257227546, 360581967243298307, 360581967229224320, 360581967155951466]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 91920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 91900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360597422497426921, 360597478152424573⟩, ⟨(-1429560521604165723), (-1426105219270061231)⟩, true⟩

def words03 : List Nat := [360581967137328813, 360581967079199287, 360581967054817348, 360581967056147099, 360581967016311639, 360581966870901394, 360581966725229553, 360581966721534813, 360581966891321732, 360581967061406746]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 91930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 91900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575523104976639, 360575578772626362⟩, ⟨583925673271441852, 587382138899973892⟩, true⟩

def words04 : List Nat := [360581967160355834, 360581967161685202, 360581967240341623, 360581967339678995, 360581967340811575, 360581967338639864, 360581967266148911, 360581967134435774, 360581967002483029, 360581966832864535]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 91940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 91900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360559578055939574, 360559633736124987⟩, ⟨2050223110059233927, 2053680728406099153⟩, true⟩

def words05 : List Nat := [360581966813115271, 360581966863115494, 360581966864314295, 360581966829527443, 360581966740465033, 360581966601962086, 360581966463071277, 360581966442547197, 360581966303907112, 360581966062445193]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 91950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 91900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360603487905435496, 360603543598163726⟩, ⟨(-1987967651205931598), (-1984508879358897388)⟩, true⟩

def words06 : List Nat := [360581965820674354, 360581965697421095, 360581965676919231, 360581965702594320, 360581965703820704, 360581965628958404, 360581965601592875, 360581965647880891, 360581965811860353, 360581966047855924]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 91960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 91900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360576395131772790, 360576450837197754⟩, ⟨503905221249773874, 507365160875047162⟩, true⟩

def words07 : List Nat := [360581966192527069, 360581966337321005, 360581966477917483, 360581966677992914, 360581966813900141, 360581966950014844, 360581967000096241, 360581967001426213, 360581966933453803, 360581966875041580]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 91970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 91900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575905876695877, 360575961594639035⟩, ⟨548945790897511288, 552406882009762520⟩, true⟩

def words08 : List Nat := [360581966836507044, 360581966882763859, 360581966883948755, 360581966870886898, 360581966857608279, 360581966830283435, 360581966831380315, 360581966797679746, 360581966763839203, 360581966669995159]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 91980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 91900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603330728650825, 360603386459142765⟩, ⟨(-1974049672101722409), (-1970587426563738253)⟩, true⟩

def words09 : List Nat := [360581966624562319, 360581966644798658, 360581966682673354, 360581966723731751, 360581966724958558, 360581966665504850, 360581966663022546, 360581966795314618, 360581967029212302, 360581967263410505]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 91990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 91900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 91900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk919
