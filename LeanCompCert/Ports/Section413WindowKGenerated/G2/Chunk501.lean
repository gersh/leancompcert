import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk501

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

def state06 : KState := ⟨⟨360618915767738871, 360618931555866388⟩, ⟨(-1857439885559621177), (-1856904771744624067)⟩, true⟩

def words05 : List Nat := [360581906475605422, 360581906878026217, 360581907677054307, 360581908726954837, 360581909498479542, 360581910270076449, 360581910841790154, 360581911183854003, 360581911922459487, 360581912661272090]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360613406678628178, 360613422473282207⟩, ⟨(-1581027620931025695), (-1580492179713207953)⟩, true⟩

def words06 : List Nat := [360581913701887153, 360581914753878379, 360581915551301104, 360581916348766878, 360581916979915952, 360581917815826302, 360581918558399388, 360581919301071353, 360581919738267027, 360581920366891799]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360630748586562101, 360630764387751106⟩, ⟨(-2451232204883323339), (-2450696435773150869)⟩, true⟩

def words07 : List Nat := [360581921055836023, 360581921744952472, 360581922740675242, 360581923340277933, 360581923582344944, 360581923824461882, 360581924462846736, 360581925301677549, 360581926275516731, 360581927249476199]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360617888868936961, 360617904676731165⟩, ⟨(-1806049687502910699), (-1805513586911621431)⟩, true⟩

def words08 : List Nat := [360581927987521910, 360581928668026574, 360581929241321632, 360581929814796528, 360581930288515848, 360581930581065364, 360581930674882275, 360581930768771197, 360581931103763578, 360581931821300678]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360563051703019539, 360563067517334995⟩, ⟨946591074439621307, 947127502364976605⟩, true⟩

def words09 : List Nat := [360581932809049445, 360581933796891467, 360581934456996788, 360581934721309382, 360581934886112732, 360581935051093288, 360581935098020030, 360581935098714544, 360581934974182987, 360581934599055413]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk501
