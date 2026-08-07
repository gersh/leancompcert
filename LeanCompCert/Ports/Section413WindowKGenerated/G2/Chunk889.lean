import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk889

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580480147388417, 360580532047045697⟩, ⟨134557336026500026, 137673045880953476⟩, true⟩

def state01 : KState := ⟨⟨360594573204891277, 360594625116642990⟩, ⟨(-1118364267585016602), (-1115247482475113170)⟩, true⟩

def words00 : List Nat := [360582080697297267, 360582080833401697, 360582081095419532, 360582081357677121, 360582081512626606, 360582081541324947, 360582081542384110, 360582081518460294, 360582081560228989, 360582081702639379]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 88900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 88900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591956610208402, 360592008534181538⟩, ⟨(-885751970218061130), (-882634098444580250)⟩, true⟩

def words01 : List Nat := [360582081760784576, 360582081819055725, 360582081856555641, 360582082002168629, 360582082115586784, 360582082229211585, 360582082273937634, 360582082275221384, 360582082373243449, 360582082486358813]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 88910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 88900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579449163089661, 360579501099143765⟩, ⟨226434297827438747, 229553243902483937⟩, true⟩

def words02 : List Nat := [360582082596133738, 360582082607018506, 360582082608160653, 360582082555699303, 360582082503021621, 360582082418275818, 360582082416661546, 360582082438033504, 360582082439186936, 360582082379295598]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 88920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 88900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591097065649199, 360591149013800906⟩, ⟨(-809481534634516672), (-806361512661447550)⟩, true⟩

def words03 : List Nat := [360582082425890506, 360582082501886000, 360582082615308198, 360582082643406855, 360582082644618430, 360582082541244739, 360582082459192346, 360582082555631230, 360582082658609662, 360582082761873658]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 88930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 88900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592602086269672, 360592654046649670⟩, ⟨(-943392247902741799), (-940271138285305139)⟩, true⟩

def words04 : List Nat := [360582082784262242, 360582082809855840, 360582082904102074, 360582082998725895, 360582083061204411, 360582083167052362, 360582083209957736, 360582083252991953, 360582083262292582, 360582083382595469]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 88940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 88900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360576519880684632, 360576571853137439⟩, ⟨487263412215294283, 490385595770583363⟩, true⟩

def words05 : List Nat := [360582083628648406, 360582083874941620, 360582084052219150, 360582084138563140, 360582084192911876, 360582084247637673, 360582084321308745, 360582084340637690, 360582084341785721, 360582084281147451]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590962223409736, 360591014207981899⟩, ⟨(-797670981200759592), (-794547719448520908)⟩, true⟩

def words06 : List Nat := [360582084220222396, 360582084246667520, 360582084262206100, 360582084277973788, 360582084279168890, 360582084189632386, 360582083973710092, 360582083838990075, 360582083703886776, 360582083795606535]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585193049004950, 360585245045790778⟩, ⟨(-284337921824767272), (-281213573362602998)⟩, true⟩

def words07 : List Nat := [360582083824379897, 360582083853299718, 360582083987636954, 360582084186159935, 360582084352001751, 360582084518048240, 360582084577059151, 360582084594487940, 360582084631050563, 360582084668031902]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360577288036146234, 360577340045006073⟩, ⟨419055520746921971, 422180943616525617⟩, true⟩

def words08 : List Nat := [360582084799276335, 360582084804670204, 360582084805823883, 360582084748549632, 360582084691050319, 360582084546200255, 360582084464292488, 360582084392034867, 360582084319638994, 360582084184163468]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360594619108315873, 360594671129301997⟩, ⟨(-1123396849081753411), (-1120270347035419049)⟩, true⟩

def words09 : List Nat := [360582084131908267, 360582084077133874, 360582084091822328, 360582084093105299, 360582084038078225, 360582083858641437, 360582083678960017, 360582083678232530, 360582083820701897, 360582083963460766]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk889
