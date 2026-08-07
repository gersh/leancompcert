import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk604

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593528899795849, 360593552138009830⟩, ⟨(-678491387129500391), (-677543168101867025)⟩, true⟩

def state01 : KState := ⟨⟨360595165542949668, 360595188789149184⟩, ⟨(-777479028852597180), (-776530327457633306)⟩, true⟩

def words00 : List Nat := [360582334753031933, 360582334921517457, 360582335081658953, 360582335241945361, 360582335242724667, 360582335171461302, 360582334826865449, 360582334629064070, 360582334454084832, 360582334667756431]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594023413227407, 360594046667475100⟩, ⟨(-708474826949946025), (-707525639325147271)⟩, true⟩

def words01 : List Nat := [360582334708526841, 360582334749390544, 360582335064125987, 360582335515836161, 360582335854826648, 360582336193943957, 360582336317362678, 360582336348882470, 360582336543381711, 360582336738157063]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581414240020552, 360581437502229273⟩, ⟨53327578296477536, 54277246966663786⟩, true⟩

def words02 : List Nat := [360582336922801199, 360582336923646856, 360582336835328826, 360582336540082801, 360582336244690431, 360582335880962967, 360582335714510823, 360582335768758596, 360582335769511806, 360582335686028159]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603155934430009, 360603179204633400⟩, ⟨(-1260698200405117255), (-1259748048578053943)⟩, true⟩

def words03 : List Nat := [360582335671860821, 360582335578952868, 360582335603532876, 360582335800352486, 360582335801141673, 360582335733784111, 360582335678281712, 360582335905722017, 360582336251266512, 360582336596989946]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590052681295154, 360590075959549689⟩, ⟨(-468807387684327221), (-467856749207432267)⟩, true⟩

def words04 : List Nat := [360582336804900217, 360582336831473967, 360582337131652733, 360582337432079993, 360582337470268960, 360582337471114999, 360582337236505485, 360582336864368931, 360582336492082512, 360582336521836377]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360580528569561078, 360580551855791975⟩, ⟨107000772306663263, 107951892994146137⟩, true⟩

def words05 : List Nat := [360582336841087967, 360582337160508136, 360582337340777995, 360582337341624128, 360582337312240122, 360582337188433170, 360582337213283921, 360582337392993797, 360582337393760507, 360582337365103820]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 60450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 60400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360597970344255709, 360597993638471861⟩, ⟨(-947568290944159105), (-946616687428009613)⟩, true⟩

def words06 : List Nat := [360582337510065954, 360582337824091842, 360582338218119578, 360582338612293285, 360582338764512926, 360582338930808875, 360582339029347143, 360582339128124943, 360582339318306400, 360582339578055662]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 60460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 60400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360584569654057179, 360584592956353888⟩, ⟨(-137222224852753128), (-136270132665123706)⟩, true⟩

def words07 : List Nat := [360582339700896102, 360582339823818037, 360582339873972477, 360582340060850529, 360582340081736204, 360582340102762181, 360582340103517744, 360582339959938183, 360582339811633898, 360582339849879704]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 60470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 60400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360572127913600318, 360572151223863661⟩, ⟨615288007131346516, 616240581181381918⟩, true⟩

def words08 : List Nat := [360582340050914634, 360582340051761239, 360582339980386281, 360582339771630228, 360582339562742873, 360582339284008543, 360582339202147880, 360582339112339411, 360582339022457377, 360582338702474694]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 60480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 60400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360630036762527386, 360630060080779121⟩, ⟨(-2887922326053495192), (-2886969268746880298)⟩, true⟩

def words09 : List Nat := [360582338584400314, 360582338634986025, 360582338958598101, 360582339387507657, 360582339566786293, 360582339746126591, 360582340198540896, 360582340790152525, 360582341579585703, 360582342369191761]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 60490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 60400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 60400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk604
