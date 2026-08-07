import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk549

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582478701734552, 360582497754219004⟩, ⟨(-40492131852586785), (-39785416019004801)⟩, true⟩

def state01 : KState := ⟨⟨360570548084548479, 360570567144226974⟩, ⟨614371595568676819, 615078706390675607⟩, true⟩

def words00 : List Nat := [360581773079235858, 360581772841292609, 360581772369529493, 360581771732188954, 360581771094747186, 360581770321936870, 360581769715540325, 360581769440320950, 360581769165020765, 360581768723290727]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605807847347128, 360605826914228376⟩, ⟨(-1322000387962329979), (-1321292881601003573)⟩, true⟩

def words01 : List Nat := [360581768524359617, 360581768529656842, 360581768783157937, 360581768783921313, 360581768706906713, 360581768316456311, 360581767925873913, 360581767973626800, 360581768412316504, 360581768851163228]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574605237130982, 360574624311292363⟩, ⟨391765353272763746, 392473259494673578⟩, true⟩

def words02 : List Nat := [360581769124333174, 360581769406082512, 360581769738098961, 360581770070324357, 360581770223709202, 360581770224473415, 360581770204339937, 360581769948845716, 360581769693226920, 360581769282337233]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573497190053065, 360573516271403798⟩, ⟨452695100873813505, 453403402043100253⟩, true⟩

def words03 : List Nat := [360581769274694857, 360581769397266645, 360581769397946895, 360581769355119427, 360581769290268406, 360581769142372572, 360581769105451248, 360581769121313998, 360581769121994315, 360581768972569490]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604048206149448, 360604067294718026⟩, ⟨(-1225982678924852039), (-1225273981172373195)⟩, true⟩

def words04 : List Nat := [360581769003291092, 360581769350787594, 360581769617912138, 360581769885164448, 360581769885880996, 360581769802719693, 360581769481255754, 360581769315800806, 360581769314273668, 360581769720858181]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360595990438670035, 360596009534507611⟩, ⟨(-783164702648462805), (-782455605428238371)⟩, true⟩

def words05 : List Nat := [360581769912784357, 360581770104783758, 360581770560718274, 360581771232885166, 360581771749134126, 360581772265493570, 360581772524904400, 360581772525668370, 360581772714032575, 360581772973938695]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360566270719876064, 360566289822907260⟩, ⟨850291779490870420, 851001272108492414⟩, true⟩

def words06 : List Nat := [360581773213675661, 360581773214439692, 360581773124252952, 360581772853178332, 360581772581972003, 360581772227774607, 360581772039467300, 360581771761402739, 360581771483265049, 360581771017597246]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592606861469970, 360592625971726667⟩, ⟨(-597661080423607658), (-596951190585445290)⟩, true⟩

def words07 : List Nat := [360581770736601058, 360581770447810589, 360581770199371087, 360581770200135304, 360581769911548421, 360581769341212053, 360581768770753018, 360581768299240600, 360581768364704565, 360581768562974818]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360577509809175228, 360577528926713234⟩, ⟨232343935581067257, 233054225779880135⟩, true⟩

def words08 : List Nat := [360581768563662319, 360581768541752781, 360581768454520549, 360581768576480747, 360581768577131453, 360581768471310607, 360581768226356648, 360581767816410585, 360581767406337079, 360581767046840164]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360540972903951975, 360540992028697120⟩, ⟨2241792271836542638, 2242502958391420826⟩, true⟩

def words09 : List Nat := [360581767150076104, 360581767330534490, 360581767331216476, 360581767297916208, 360581767069192717, 360581766646847855, 360581766224294386, 360581766010190773, 360581765550297988, 360581764809758783]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk549
