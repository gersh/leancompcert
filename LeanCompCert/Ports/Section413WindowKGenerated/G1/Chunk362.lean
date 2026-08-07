import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk362

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362500845275615888, 362500863719534792⟩, ⟨(-574862732821061710), (-574411509806133808)⟩, true⟩

def state01 : KState := ⟨⟨362480641394006906, 362480659848552346⟩, ⟨156503196403041555, 156954804152228789⟩, true⟩

def words00 : List Nat := [371284996742233636, 371284996743413189, 371284996291367625, 371284996353214836, 371284996538276781, 371284996539455335, 371284995845487350, 371284995116159575, 371284994417880968, 371284994419227636]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 36200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 36200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483420854966933, 362483439320123490⟩, ⟨55853153841316663, 56305145874522949⟩, true⟩

def words01 : List Nat := [371284994489042402, 371284994679012289, 371284994866316155, 371284994867497172, 371284994269505090, 371284993903875489, 371284993932339086, 371284993933543765, 371284993893644016, 371284993852036095]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 36210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 36200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485124402238121, 362485142877933433⟩, ⟨(-5824721077296182), (-5372347275999666)⟩, true⟩

def words02 : List Nat := [371284994332066658, 371284994476379358, 371284994857654278, 371284995239397837, 371284995393185777, 371284995394364979, 371284994645157492, 371284994374421689, 371284994592217527, 371284994597530574]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 36220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 36200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474577172880669, 362474595659345272⟩, ⟨376461099256747770, 376913863283103148⟩, true⟩

def words03 : List Nat := [371284994598416304, 371284994587648441, 371284995123401805, 371284995419098273, 371284995945804749, 371284996472922474, 371284996961965034, 371284996963144369, 371284996437783260, 371284996152261473]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 36230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 36200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362465371904641426, 362465390401609230⟩, ⟨710142267515446601, 710595412231872727⟩, true⟩

def words04 : List Nat := [371284996339884615, 371284996341064040, 371284995801594419, 371284995265949454, 371284994729889396, 371284994239603041, 371284993468856410, 371284993331291944, 371284993193325379, 371284993033670799]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 36240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 36200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491132397496503, 362491150905134209⟩, ⟨(-223796195468837213), (-223342663916448593)⟩, true⟩

def words05 : List Nat := [371284992713373670, 371284992934424953, 371284993469715841, 371284993470895671, 371284992992771333, 371284992399887893, 371284991806536640, 371284991720580774, 371284991426027429, 371284991597229947]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 36250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 36200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362462675581235307, 362462694099517456⟩, ⟨808095209527746030, 808549127101997592⟩, true⟩

def words06 : List Nat := [371284991684818303, 371284991685998322, 371284990760488290, 371284990595429534, 371284990494360085, 371284990495540166, 371284989548230521, 371284988313619453, 371284987078607934, 371284986603711060]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 36260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 36200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362468433417903252, 362468451946818239⟩, ⟨599262852302724611, 599717155585475097⟩, true⟩

def words07 : List Nat := [371284985989905548, 371284985722041182, 371284985453778560, 371284985189600154, 371284984295727585, 371284983626005462, 371284983043958953, 371284983045150658, 371284982642457894, 371284982188151908]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 36270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 36200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362462098083094697, 362462116622598906⟩, ⟨829166055762793990, 829620743273833770⟩, true⟩

def words08 : List Nat := [371284981733350336, 371284981509342991, 371284980907391118, 371284980812517053, 371284980717291906, 371284980396223887, 371284979063062499, 371284978410617453, 371284977757546717, 371284977486287907]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 36280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 36200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362462314232467005, 362462332782710363⟩, ⟨821368663353135292, 821823740641706656⟩, true⟩

def words09 : List Nat := [371284976857239017, 371284976226213382, 371284975720988858, 371284975722291621, 371284975532662490, 371284975230712821, 371284974928373853, 371284974558576581, 371284973177422293, 371284972555179832]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 36290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 36200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 36200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk362
