import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk021

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362532229349076629, 362532229396516299⟩, ⟨(-111840565412091544), (-111840497765822688)⟩, true⟩

def state01 : KState := ⟨⟨361897996954033422, 361897997001944078⟩, ⟨1223821075811221593, 1223821144449017393⟩, true⟩

def words00 : List Nat := [371279133492831091, 371279133492883927, 371278971009276212, 371278808902704215, 371278646950132399, 371278550059660694, 371278367722689789, 371278255956637786, 371278144296558262, 371278007023009964]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 2100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 2100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362750738942589148, 362750738990980331⟩, ⟨(-578362146284338024), (-578362076630199330)⟩, true⟩

def words01 : List Nat := [371277732266996395, 371277679678339770, 371277796349450891, 371277796349504852, 371277787339390702, 371277741551015602, 371277801782259158, 371277801782317583, 371277926690623072, 371278055315058502]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 2110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 2100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362026292667720411, 362026292716593675⟩, ⟨958570243906373103, 958570314584999957⟩, true⟩

def words02 : List Nat := [371278131072454656, 371278131072507970, 371277913889069004, 371277807686738479, 371277701584337457, 371277615666862398, 371277238187472950, 371276861034610029, 371276484236024634, 371276325728135929]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 2120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 2100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361924665540442248, 361924665589798102⟩, ⟨1178037691519104840, 1178037763228170142⟩, true⟩

def words03 : List Nat := [371276121208143682, 371276127865880817, 371276135224379585, 371276135224433571, 371275957320202872, 371275783510995802, 371275653286118788, 371275653286172554, 371275407882037642, 371275150525886032]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 2130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 2100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362401220205117368, 362401220254957501⟩, ⟨158556342075404859, 158556414823306245⟩, true⟩

def words04 : List Nat := [371274893410118938, 371274852840748477, 371274851692727211, 371274959122166967, 371275017780956170, 371275017781010256, 371274874204519478, 371274878762210706, 371274967424586729, 371274967424642760]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 2140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 2100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362611369899295405, 362611369949630816⟩, ⟨(-293487674709035775), (-293487600893798447)⟩, true⟩

def words05 : List Nat := [371274933139621183, 371274894045367134, 371275029925454387, 371275099260234291, 371275230686826168, 371275361991578798, 371275492153224757, 371275492153279300, 371275496060259961, 371275558935797499]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 2150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 2100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362549391342728985, 362549391393550520⟩, ⟨(-158367030594235050), (-158366955726410772)⟩, true⟩

def words06 : List Nat := [371275834051673193, 371275907810165298, 371275936682427630, 371275965528035049, 371276056717128500, 371276065399106311, 371276181706726040, 371276297907122378, 371276411229563899, 371276444845542040]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 2160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 2100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362914175453104030, 362914175504420498⟩, ⟨(-952354374475433878), (-952354298531103410)⟩, true⟩

def words07 : List Nat := [371276606817798934, 371276768641005754, 371277068561340683, 371277089306087386, 371277089306130027, 371277072644485866, 371277122925771815, 371277122925832985, 371277315734391201, 371277516036960112]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 2170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 2100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362164441546754757, 362164441598567671⟩, ⟨684744326958420530, 684744403987549966⟩, true⟩

def words08 : List Nat := [371277715281717567, 371277715281772522, 371277693205521157, 371277748796267329, 371277819819012177, 371277819819067227, 371277615033552597, 371277410435245095, 371277206023849458, 371277110276187557]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 2180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 2100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨361759090508142766, 361759090560455524⟩, ⟨1574981431233729911, 1574981509360097241⟩, true⟩

def words09 : List Nat := [371276967570302772, 371276909249493770, 371276850981854098, 371276762081862688, 371276399663459038, 371276101206181891, 371275803020572211, 371275642750064670, 371275316803848706, 371274991246528296]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 2190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 2100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 2100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk021
