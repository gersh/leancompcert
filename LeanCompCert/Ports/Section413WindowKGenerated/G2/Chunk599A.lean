import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk599A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360591054366742750, 360591077206692759⟩, ⟨(-533826453096212443), (-532902189759453557)⟩, true⟩

def state01 : KState := ⟨⟨360601307026746051, 360601329874675886⟩, ⟨(-1148182475355993604), (-1147257733987409102)⟩, true⟩

def words00 : List Nat := [360582180825246108, 360582180802861233, 360582180588210619, 360582180536283323, 360582180484122680, 360582180386871259, 360582180387619260, 360582180247663500, 360582180186956882, 360582180507548190]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 59900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 59900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360553355349948665, 360553378205779167⟩, ⟨1724955473787826861, 1725880688525504237⟩, true⟩

def words01 : List Nat := [360582181051034761, 360582181594663910, 360582181923961559, 360582182104644751, 360582182136799045, 360582182169173520, 360582182169858879, 360582182107625357, 360582181767848456, 360582181288030928]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 59910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 59900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592868271272757, 360592891135014902⟩, ⟨(-642851368740809605), (-641925679898969185)⟩, true⟩

def words02 : List Nat := [360582180808024251, 360582180606930007, 360582180655133243, 360582180762992205, 360582180763768254, 360582180603142567, 360582180359539058, 360582180106003654, 360582179876343957, 360582180055942320]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 59920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 59900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591994984267734, 360592017855994400⟩, ⟨(-590477461981276732), (-589551294587705438)⟩, true⟩

def words03 : List Nat := [360582180095916579, 360582180135974296, 360582180378754536, 360582180841657812, 360582181233227859, 360582181624921819, 360582181876419446, 360582181999650222, 360582182164427516, 360582182329483536]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 59930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 59900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360601245279077340, 360601268158712469⟩, ⟨(-1145062019283782067), (-1144135377819096447)⟩, true⟩

def words04 : List Nat := [360582182485899266, 360582182698657219, 360582182705872362, 360582182713174915, 360582182713878091, 360582182647026337, 360582182921350645, 360582183195841186, 360582183330851334, 360582183650066757]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 59940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 59900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk599A
