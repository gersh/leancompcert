import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk616

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583781779546581, 360583805987965768⟩, ⟨(-78690570550179322), (-77683166989346088)⟩, true⟩

def state01 : KState := ⟨⟨360606838116619441, 360606862333178404⟩, ⟨(-1499043493242682305), (-1498035588230606455)⟩, true⟩

def words00 : List Nat := [360582545145744228, 360582545504725356, 360582546126812371, 360582546749044779, 360582547124094498, 360582547236832325, 360582547243349945, 360582547250107870, 360582547519944714, 360582547915489508]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360601564994537864, 360601589219323384⟩, ⟨(-1174111885695336049), (-1173103473805366111)⟩, true⟩

def words01 : List Nat := [360582548110647960, 360582548305889583, 360582548764274549, 360582549437580166, 360582550043287430, 360582550649116135, 360582551056757064, 360582551202188147, 360582551511845189, 360582551821783498]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596491904550303, 360596516137477860⟩, ⟨(-861542147421559680), (-860533233777754002)⟩, true⟩

def words02 : List Nat := [360582552124196087, 360582552385653339, 360582552475162602, 360582552564755974, 360582552565482379, 360582552493981651, 360582552787093219, 360582553080376721, 360582553241341288, 360582553468792008]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360610828776439192, 360610853017518950⟩, ⟨(-1745259026258850117), (-1744249610153731069)⟩, true⟩

def words03 : List Nat := [360582553959183078, 360582554449820709, 360582554852530269, 360582554993257948, 360582554994068460, 360582554879358944, 360582554912021097, 360582555191330121, 360582555651111079, 360582556111074316]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360625344920168972, 360625369169498668⟩, ⟨(-2640127099661503481), (-2639117174990858885)⟩, true⟩

def words04 : List Nat := [360582556437720727, 360582556921674898, 360582557668482098, 360582558415525043, 360582559095119107, 360582559698291067, 360582560169254147, 360582560640296507, 360582561104025966, 360582561799383166]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360598052630996657, 360598076888465073⟩, ⟨(-957316329265987138), (-956305902802277512)⟩, true⟩

def words05 : List Nat := [360582562757392337, 360582563715536112, 360582564541514095, 360582565227049520, 360582565678060445, 360582566129295819, 360582566843163083, 360582567295278524, 360582567547596168, 360582567800016909]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 61650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 61600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360639707935644870, 360639732201280905⟩, ⟨(-3526054500214028111), (-3525043570094294297)⟩, true⟩

def words06 : List Nat := [360582568269525001, 360582568901640705, 360582569445363629, 360582569989222091, 360582570310551864, 360582570590687441, 360582571133486345, 360582571676531087, 360582572421383904, 360582573349144662]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 61660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 61600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360630329152278835, 360630353426146137⟩, ⟨(-2947574210790678828), (-2946562773007949426)⟩, true⟩

def words07 : List Nat := [360582574117109117, 360582574885147210, 360582575915789737, 360582577112873789, 360582578243534601, 360582579374301453, 360582580257986128, 360582580879947688, 360582581655169553, 360582582430653069]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 61670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 61600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360636224397182247, 360636248679190785⟩, ⟨(-3311270745354514418), (-3310258805379572062)⟩, true⟩

def words08 : List Nat := [360582583468555550, 360582584244844104, 360582584859242604, 360582585473730129, 360582585928698231, 360582586560020178, 360582587453752433, 360582588347627305, 360582589109395866, 360582589980103729]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 61680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 61600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360628977124195002, 360629001414380603⟩, ⟨(-2864222692237224367), (-2863210247780408291)⟩, true⟩

def words09 : List Nat := [360582590840870067, 360582591701850239, 360582592525302393, 360582593140711737, 360582593533214897, 360582593925764739, 360582594513800688, 360582595308178983, 360582596061007976, 360582596814004914]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 61690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 61600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 61600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk616
