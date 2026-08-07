import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk460

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362466905882967000, 362466936251622201⟩, ⟨854517639656829784, 855461474896561700⟩, true⟩

def state01 : KState := ⟨⟨362490163986626506, 362490194368940704⟩, ⟨(-215391582861043064), (-214447119239995266)⟩, true⟩

def words00 : List Nat := [371285532865766611, 371285532867463530, 371285533087359457, 371285533410294529, 371285533657471955, 371285533658997549, 371285533276828876, 371285533206534530, 371285533486699236, 371285533589578378]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 46000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 46000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489879537864318, 362489909934082517⟩, ⟨(-202330228217479865), (-201385124802735733)⟩, true⟩

def words01 : List Nat := [371285533604646057, 371285533620193247, 371285533799467121, 371285533801148149, 371285533830031233, 371285533917472676, 371285534003376782, 371285534004932600, 371285533897329568, 371285533994298446]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 46010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 46000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474426357517300, 362474456767312525⟩, ⟨508941955080530275, 509887683381495195⟩, true⟩

def words02 : List Nat := [371285534561789741, 371285534563316073, 371285534502158028, 371285534368431677, 371285534234123127, 371285534115543132, 371285533877508836, 371285533995247069, 371285534056268757, 371285534057848730]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 46020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 46000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489156304650272, 362489186728279669⟩, ⟨(-169109050470646049), (-168162685313771255)⟩, true⟩

def words03 : List Nat := [371285534006960414, 371285534197554122, 371285534698275199, 371285534699801782, 371285534572260248, 371285534341710139, 371285534228251767, 371285534229933668, 371285534192118188, 371285534273178482]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 46030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 46000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491684455657535, 362491714893065146⟩, ⟨(-285631199852997343), (-284684200276445707)⟩, true⟩

def words04 : List Nat := [371285534319402318, 371285534320929133, 371285533738876562, 371285533520758388, 371285533301896275, 371285533227261363, 371285533008633551, 371285532790941518, 371285532823997670, 371285532959984943]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 46040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 46000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362461280452953529, 362461310904113671⟩, ⟨1114739181567477791, 1115686814517380919⟩, true⟩

def words05 : List Nat := [371285533565970308, 371285534172537178, 371285534629773151, 371285534631300410, 371285534460579092, 371285534385067294, 371285534414391865, 371285534415919254, 371285533894946667, 371285533370777097]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 46050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 46000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476820414250471, 362476850879075145⟩, ⟨398978566836254926, 399926829245017036⟩, true⟩

def words06 : List Nat := [371285532845935915, 371285532792329236, 371285532632260118, 371285532763655838, 371285532793532815, 371285532795061602, 371285532297087527, 371285531997252610, 371285531729003349, 371285531730589038]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 46060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 46000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362471584345267315, 362471614824043267⟩, ⟨640325525369797196, 641274430582210392⟩, true⟩

def words07 : List Nat := [371285531543319007, 371285531355857166, 371285531448893973, 371285531562355064, 371285531745339102, 371285531928881831, 371285532112285831, 371285532113813970, 371285531669928163, 371285531369845833]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 46070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 46000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362444731533314362, 362444762025714241⟩, ⟨1877792259053893701, 1878741792128686925⟩, true⟩

def words08 : List Nat := [371285531068900323, 371285530852000707, 371285530007626798, 371285529164216929, 371285528320277854, 371285527565442097, 371285526574602335, 371285525882965810, 371285525190813776, 371285524485947018]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 46080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 46000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492106968921110, 362492137475115009⟩, ⟨(-305970187123362427), (-305020018212365039)⟩, true⟩

def words09 : List Nat := [371285523602593791, 371285523189930142, 371285522831920140, 371285522833452216, 371285522402534677, 371285521861448651, 371285521319745453, 371285521168770439, 371285520987115302, 371285521132341266]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 46090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 46000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 46000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk460
