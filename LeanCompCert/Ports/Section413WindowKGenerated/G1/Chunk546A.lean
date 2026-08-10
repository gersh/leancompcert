import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk546A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473058998460299, 362473102381299741⟩, ⟨642416439576525489, 644016606083062645⟩, true⟩

def state01 : KState := ⟨⟨362462007416364116, 362462050815535409⟩, ⟨1245951129222028605, 1247552187532604559⟩, true⟩

def words00 : List Nat := [371284897461529350, 371284897463366791, 371284897222922495, 371284896982272218, 371284896740926814, 371284896567831297, 371284896267795965, 371284896039596521, 371284895810762875, 371284895572677556]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 54600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 54600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497641937037109, 362497685352767944⟩, ⟨(-700235761716874617), (-698633799005539221)⟩, true⟩

def words01 : List Nat := [371284895155605240, 371284895012294078, 371284894944726519, 371284894946594635, 371284894803364035, 371284894555082937, 371284894390672594, 371284894392695172, 371284894545176212, 371284894781394196]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 54610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 54600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362493968555167063, 362494011987513455⟩, ⟨(-499664139090661348), (-498061268753395190)⟩, true⟩

def words02 : List Nat := [371284894918869061, 371284894920706269, 371284894772385277, 371284894867243058, 371284894985953984, 371284894987811135, 371284894907842196, 371284894825716671, 371284894993477154, 371284895162473581]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 54620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 54600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481211889125100, 362481255338001977⟩, ⟨197383317908295244, 198987091391476426⟩, true⟩

def words03 : List Nat := [371284895665359980, 371284896168990293, 371284896672173440, 371284896776132753, 371284896877922968, 371284896980575415, 371284897253343550, 371284897255184892, 371284897186816304, 371284897122251455]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 54630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 54600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492186105174512, 362492229570514150⟩, ⟨(-402206085556668454), (-400601412467111972)⟩, true⟩

def words04 : List Nat := [371284897272316098, 371284897369251285, 371284897751734748, 371284898134937885, 371284898464202411, 371284898466039256, 371284898651034710, 371284898912435998, 371284899259142097, 371284899395174868]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 54640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 54600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk546A
