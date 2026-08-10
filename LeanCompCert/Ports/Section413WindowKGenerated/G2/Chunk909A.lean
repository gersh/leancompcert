import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk909A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360554846570904506, 360554900925702350⟩, ⟨2459166772405965471, 2462503209151730857⟩, true⟩

def state01 : KState := ⟨⟨360569943291597636, 360569997658772004⟩, ⟨1086837460963284361, 1090175022796100219⟩, true⟩

def words00 : List Nat := [360581990873069377, 360581990697259144, 360581990558405583, 360581990350966016, 360581990143307883, 360581989905654842, 360581989731536525, 360581989678526418, 360581989625413274, 360581989464104708]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 90900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 90900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360588306954303052, 360588361333867693⟩, ⟨(-582682582376809276), (-579343894083582872)⟩, true⟩

def words01 : List Nat := [360581989333258842, 360581989323646291, 360581989401082326, 360581989402395354, 360581989400001318, 360581989285573185, 360581989175936722, 360581989243167495, 360581989314315455, 360581989385757976]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 90910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 90900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586170443997593, 360586224836083005⟩, ⟨(-388529796605019254), (-385189969860316286)⟩, true⟩

def words02 : List Nat := [360581989396380696, 360581989397700258, 360581989380417227, 360581989331811829, 360581989282860489, 360581989203350949, 360581989105067599, 360581988946575491, 360581988787835270, 360581988767307117]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 90920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 90900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360560803213292201, 360560857617740879⟩, ⟨1918315217872807824, 1921656168872440910⟩, true⟩

def words03 : List Nat := [360581988935749423, 360581989104439910, 360581989189552711, 360581989221716298, 360581989222820672, 360581989187204918, 360581989151215071, 360581989052635569, 360581988882052214, 360581988651047152]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 90930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 90900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596572543415926, 360596626960268073⟩, ⟨(-1334735743197048537), (-1331393664168081723)⟩, true⟩

def words04 : List Nat := [360581988419749126, 360581988288733147, 360581988279981991, 360581988328278237, 360581988329501986, 360581988271134515, 360581988143657604, 360581988137341239, 360581988216031185, 360581988378348490]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 90940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 90900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk909A
