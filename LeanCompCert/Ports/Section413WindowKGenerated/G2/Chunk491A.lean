import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk491A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk491A
