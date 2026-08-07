import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk491

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569879410982508, 360569894512529011⟩, ⟨589647228584931620, 590148265997751156⟩, true⟩

def state01 : KState := ⟨⟨360554284174865410, 360554299282850498⟩, ⟨1355244468810032653, 1355745822389676553⟩, true⟩

def words00 : List Nat := [360581913581300005, 360581913072372820, 360581912148822021, 360581911638929781, 360581911128877443, 360581910262401591, 360581909146267681, 360581907823566907, 360581906500790414, 360581905591593925]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 49100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 49100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360524440548637192, 360524455663003828⟩, ⟨2821092535210392880, 2821594202219634188⟩, true⟩

def words01 : List Nat := [360581905030020429, 360581904759196944, 360581904488306658, 360581903920972070, 360581903233927690, 360581902203810326, 360581901173536549, 360581900556590049, 360581899710476410, 360581898541713512]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 49110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 49100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604653412685910, 360604668533441948⟩, ⟨(-1119358518304748765), (-1118856537416940009)⟩, true⟩

def words02 : List Nat := [360581897372844874, 360581896617345182, 360581896068497803, 360581895932901709, 360581895797259029, 360581895297349932, 360581895089498962, 360581895005383881, 360581895145045191, 360581895609271528]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 49120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 49100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360586250275249336, 360586265402468621⟩, ⟨(-215165478479864475), (-214663180023108131)⟩, true⟩

def words03 : List Nat := [360581895823470409, 360581896037728892, 360581896243559108, 360581896704140942, 360581896986750185, 360581897269458426, 360581897270065558, 360581897236083170, 360581897001589834, 360581897091281973]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 49130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 49100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360558623926295703, 360558639059883925⟩, ⟨1142548503928163269, 1143051115387048395⟩, true⟩

def words04 : List Nat := [360581897503578342, 360581897504255501, 360581897502802034, 360581897295031733, 360581897087159430, 360581896776702133, 360581896675367390, 360581896348988328, 360581896022549891, 360581895440664944]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 49140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 49100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360575496743735868, 360575511883714693⟩, ⟨313143629116515233, 313646554706254409⟩, true⟩

def words05 : List Nat := [360581894968051335, 360581894689012132, 360581894409789588, 360581894076920454, 360581893758056596, 360581893093217068, 360581892428274902, 360581892176050326, 360581892129859620, 360581892000775439]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590826841746797, 360590841988186194⟩, ⟨(-440798588211463040), (-440295344988479544)⟩, true⟩

def words06 : List Nat := [360581891871609261, 360581891420402825, 360581890699878123, 360581890308424122, 360581889916804760, 360581889422750516, 360581888984002297, 360581888330465785, 360581887676814441, 360581887617825850]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567157986510693, 360567173139324045⟩, ⟨723219971014135220, 723723527677002796⟩, true⟩

def words07 : List Nat := [360581888212755846, 360581888807792888, 360581889132855541, 360581889269227636, 360581889269805182, 360581889127405571, 360581889253872456, 360581889254550246, 360581889247687000, 360581888949158877]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573927635916896, 360573942795131330⟩, ⟨390269675780082872, 390773547280643082⟩, true⟩

def words08 : List Nat := [360581888650494552, 360581888207484984, 360581888276055760, 360581888470393542, 360581888471024162, 360581888317163007, 360581887750215989, 360581887490130419, 360581887229866233, 360581886961573303]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587516170059109, 360587531335731012⟩, ⟨(-278251759400573337), (-277747570225768349)⟩, true⟩

def words09 : List Nat := [360581886800682001, 360581886388379438, 360581885975955810, 360581886186887414, 360581886296299999, 360581886405830683, 360581886406435813, 360581886240953072, 360581886059139326, 360581886174652462]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk491
