import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk542A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603672102259964, 360603690652620482⟩, ⟨(-1184224127890208753), (-1183544803292564741)⟩, true⟩

def state01 : KState := ⟨⟨360582026597803122, 360582045155340929⟩, ⟨(-11095948430705875), (-10416234788959755)⟩, true⟩

def words00 : List Nat := [360581854547326492, 360581854548079495, 360581854611870240, 360581854762936630, 360581854763566967, 360581854755755859, 360581854408092791, 360581853853369591, 360581853298504601, 360581853012882960]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360532376628207984, 360532395192829916⟩, ⟨2680742911803825518, 2681423009512462662⟩, true⟩

def words01 : List Nat := [360581853175882150, 360581853339018625, 360581853339691135, 360581853266719303, 360581852853950188, 360581852206878325, 360581851559601192, 360581851251932588, 360581850604535269, 360581849693189792]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360561465453190545, 360561484024933473⟩, ⟨1103396416921592873, 1104076900764710425⟩, true⟩

def words02 : List Nat := [360581848781707570, 360581848096454903, 360581847673444841, 360581847216213663, 360581846758947937, 360581846010250918, 360581845120690955, 360581844502837116, 360581843884796044, 360581843178552590]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360565935252386048, 360565953831294891⟩, ⟨860984938746137868, 861665811232509778⟩, true⟩

def words03 : List Nat := [360581842803808215, 360581842259362370, 360581841714792418, 360581841448301005, 360581841409179200, 360581841284599083, 360581841159924735, 360581840836281899, 360581840292413945, 360581840000381037]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360550719299426586, 360550737885442320⟩, ⟨1686279898460349733, 1686961156458733997⟩, true⟩

def words04 : List Nat := [360581839708113127, 360581839466887089, 360581839036235469, 360581838312748487, 360581837589166558, 360581836698773424, 360581835979087737, 360581835372935586, 360581834766726772, 360581833943625892]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk542A
