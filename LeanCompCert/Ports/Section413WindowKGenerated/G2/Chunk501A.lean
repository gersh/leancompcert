import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk501A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360557048758626793, 360557064507470354⟩, ⟨1243466943426177943, 1244000087936491869⟩, true⟩

def state01 : KState := ⟨⟨360580226402597415, 360580242157950390⟩, ⟨82185923968253027, 82719394633467069⟩, true⟩

def words00 : List Nat := [360581894353500342, 360581894256115420, 360581894223959647, 360581893952303935, 360581893680550191, 360581893146078361, 360581892982628201, 360581893047556465, 360581893048172525, 360581892914179356]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 50100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 50100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360601890252970545, 360601906014862862⟩, ⟨(-1003567792370524167), (-1003033993986670185)⟩, true⟩

def words01 : List Nat := [360581893246203363, 360581893611365973, 360581893966750493, 360581893967442190, 360581893925712813, 360581893543184365, 360581893160532939, 360581892964751553, 360581893364613561, 360581893764628696]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 50110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 50100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604012121181902, 360604027889665111⟩, ⟨(-1110071122316474496), (-1109536993564985120)⟩, true⟩

def words02 : List Nat := [360581893964210476, 360581893992456263, 360581894417717721, 360581894843165025, 360581895159944328, 360581895208891762, 360581895209523520, 360581894906023661, 360581894695300963, 360581895137604211]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 50120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 50100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360611634867786983, 360611650642781742⟩, ⟨(-1492192404473116597), (-1491657949264902523)⟩, true⟩

def words03 : List Nat := [360581895976708821, 360581896815912560, 360581897374550010, 360581897944693878, 360581898319361762, 360581898694197622, 360581899392861370, 360581900188714947, 360581900782685389, 360581901376726720]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 50130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 50100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360613576398036943, 360613592179575956⟩, ⟨(-1589624702013415425), (-1589089918644688503)⟩, true⟩

def words04 : List Nat := [360581901671530793, 360581902212204530, 360581902985300694, 360581903758498375, 360581904190366752, 360581904225637128, 360581904657582759, 360581905089734398, 360581905440698149, 360581906073244185]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 50140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 50100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk501A
