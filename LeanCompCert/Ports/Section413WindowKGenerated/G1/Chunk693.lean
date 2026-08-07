import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk693

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480168993984150, 362480240210906866⟩, ⟨354603135710947499, 357936319694063617⟩, true⟩

def state01 : KState := ⟨⟨362465391400199763, 362465462638190594⟩, ⟨1378788479883912737, 1382123123999773409⟩, true⟩

def words00 : List Nat := [371285405252046592, 371285405254417056, 371285405066718655, 371285404878191758, 371285404688741263, 371285404551876555, 371285404309787701, 371285404156322576, 371285404002105923, 371285403817298945]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 69300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 69300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493074771641355, 362493146031089377⟩, ⟨(-540098452090504079), (-536762320670108153)⟩, true⟩

def words01 : List Nat := [371285403531211977, 371285403354032224, 371285403203266520, 371285403205678802, 371285403061532369, 371285402884544645, 371285402734775627, 371285402737412691, 371285402775076495, 371285402889463173]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 69310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 69300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486528020495534, 362486599301364025⟩, ⟨(-86266455356611402), (-82928838958915332)⟩, true⟩

def words02 : List Nat := [371285402959284489, 371285402961675307, 371285403007778170, 371285403128735839, 371285403276366422, 371285403278744302, 371285403213150830, 371285403148196924, 371285403152128686, 371285403172086229]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 69320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 69300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468999870052637, 362469071172224027⟩, ⟨1129074712198387987, 1132413805636329337⟩, true⟩

def words03 : List Nat := [371285403286839684, 371285403402529374, 371285403480818866, 371285403483190563, 371285403284360254, 371285403101893860, 371285402940396137, 371285402942769160, 371285402726218710, 371285402493332137]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 69330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 69300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477517433838888, 362477588757281545⟩, ⟨538490076863550561, 541830645357475917⟩, true⟩

def words04 : List Nat := [371285402259418866, 371285402234154302, 371285402206652680, 371285402260934496, 371285402262790037, 371285402259802808, 371285401979114742, 371285401872128950, 371285401763970546, 371285401744236953]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 69340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 69300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362473596034956429, 362473667380033942⟩, ⟨810486935256063926, 813829004236067932⟩, true⟩

def words05 : List Nat := [371285401633351453, 371285401523730772, 371285401483215731, 371285401485854304, 371285401453841983, 371285401405722576, 371285401356780554, 371285401293037836, 371285400951705330, 371285400785516008]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 69350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 69300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471924038428071, 362471995404663224⟩, ⟨926471245349908493, 929814781933062793⟩, true⟩

def words06 : List Nat := [371285400641660123, 371285400644033059, 371285400419516488, 371285400152328446, 371285399884260636, 371285399680725820, 371285399403559960, 371285399307232337, 371285399210070317, 371285399106291206]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 69360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 69300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484013569860133, 362484084957503150⟩, ⟨87786074136672496, 91131095890758364⟩, true⟩

def words07 : List Nat := [371285398928823249, 371285398945805259, 371285399149990607, 371285399152363757, 371285399080084201, 371285398959646754, 371285398838257089, 371285398705129080, 371285398480506742, 371285398464218209]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 69370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 69300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475028384584110, 362475099793659260⟩, ⟨711179537960985646, 714526046781923986⟩, true⟩

def words08 : List Nat := [371285398447085639, 371285398423545627, 371285398149500462, 371285398084045172, 371285398017345817, 371285398014924886, 371285397735309867, 371285397435311364, 371285397134353929, 371285397041775443]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 69380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 69300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468955924348990, 362469027354841519⟩, ⟨1132605638025039011, 1135953633109477979⟩, true⟩

def words09 : List Nat := [371285396895021351, 371285396799481221, 371285396703110960, 371285396607828867, 371285396366429212, 371285396189762692, 371285396011898023, 371285395990881581, 371285395795976135, 371285395562811397]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 69390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 69300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 69300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk693
