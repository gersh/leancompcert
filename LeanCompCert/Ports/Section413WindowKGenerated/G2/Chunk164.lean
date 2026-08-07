import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk164

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360668782917229547, 360668784450430925⟩, ⟨(-1411739720191880489), (-1411722697386160939)⟩, true⟩

def state01 : KState := ⟨⟨360620821172859694, 360620822708031415⟩, ⟨(-625536758026564569), (-625519702897453777)⟩, true⟩

def words00 : List Nat := [360582710693492183, 360582710693698912, 360582712035750913, 360582713863539754, 360582713863713341, 360582713448183988, 360582712023211613, 360582708728004891, 360582705433157027, 360582706828261904]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 16400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 16400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360535499257315232, 360535500794433983⟩, ⟨775389175800476269, 775406262890289257⟩, true⟩

def words01 : List Nat := [360582712854122795, 360582718879290152, 360582723030027702, 360582725313274260, 360582725313450471, 360582724790606732, 360582727445477838, 360582727445684704, 360582726950678363, 360582724074756169]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 16410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 16400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360665728504263432, 360665730043337765⟩, ⟨(-1363430844752125626), (-1363413725542212678)⟩, true⟩

def words02 : List Nat := [360582722023325609, 360582726290225085, 360582731075550039, 360582735860330678, 360582737507197695, 360582737507404769, 360582740396462672, 360582743689239144, 360582746858367351, 360582751908985492]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 16420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 16400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360640304298770579, 360640305839816484⟩, ⟨(-945372950589978446), (-945355798977301644)⟩, true⟩

def words03 : List Nat := [360582755089079647, 360582758268810369, 360582765142092581, 360582774847976393, 360582782724006109, 360582790599114396, 360582796605470944, 360582798947328074, 360582802445482344, 360582805943278725]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 16430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 16400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360608022899456644, 360608024442456587⟩, ⟨(-414903852426403131), (-414886668679730865)⟩, true⟩

def words04 : List Nat := [360582811496503461, 360582813386183407, 360582813386373147, 360582812156404892, 360582810926554738, 360582806102806328, 360582803823397825, 360582804527408733, 360582804527593449, 360582804901475508]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 16440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 16400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360734903307573384, 360734904852530088⟩, ⟨(-2502669742640556780), (-2502652526695266680)⟩, true⟩

def words05 : List Nat := [360582810119871386, 360582815337695267, 360582824239687364, 360582831662546886, 360582835983283921, 360582840303514093, 360582844503329181, 360582851110930231, 360582860348871054, 360582869585736135]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 16450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 16400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360626053761707557, 360626055308640998⟩, ⟨(-710980417759144774), (-710963169267315812)⟩, true⟩

def words06 : List Nat := [360582876460169289, 360582879679777833, 360582885268036894, 360582890855681408, 360582894479469877, 360582894479677446, 360582894449906897, 360582891620041441, 360582888790479905, 360582890766763316]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 16460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 16400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541997296336221, 360541998845227871⟩, ⟨673490084097996830, 673507364851408268⟩, true⟩

def words07 : List Nat := [360582891787543070, 360582892808235046, 360582892808420947, 360582891020822684, 360582885582928903, 360582879201475698, 360582872820736742, 360582870115001137, 360582869490370818, 360582867010570797]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 16470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 16400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360675738161638860, 360675739712491021⟩, ⟨(-1531086462975232898), (-1531069149902910482)⟩, true⟩

def words08 : List Nat := [360582865724460002, 360582869517071839, 360582875645887113, 360582881773999353, 360582884305791341, 360582884305999213, 360582885743998668, 360582888297874192, 360582891370862254, 360582897001321116]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 16480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 16400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360628977882019234, 360628979434854278⟩, ⟨(-759576783170578837), (-759559437390803261)⟩, true⟩

def words09 : List Nat := [360582900221152093, 360582903440619172, 360582910327281614, 360582919047869409, 360582926793702113, 360582934538629624, 360582939831105340, 360582942739045336, 360582945529319333, 360582948319322444]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 16490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 16400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 16400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk164
