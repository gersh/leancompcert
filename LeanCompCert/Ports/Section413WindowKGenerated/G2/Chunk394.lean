import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk394

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580262454525959, 360580272004790501⟩, ⟨82225160741528626, 82479488192482598⟩, true⟩

def state01 : KState := ⟨⟨360639827520069587, 360639837075376086⟩, ⟨(-2265108571730929458), (-2264854045602479026)⟩, true⟩

def words00 : List Nat := [360582365471376523, 360582366079681508, 360582366413863444, 360582366748121020, 360582366748612944, 360582366466080492, 360582366696153536, 360582367054651295, 360582368055641680, 360582369514400661]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360614090539635965, 360614100100023021⟩, ⟨(-1250717430879620080), (-1250462704501032412)⟩, true⟩

def words01 : List Nat := [360582370557019012, 360582371599638100, 360582372739130310, 360582374200769401, 360582375499570369, 360582376798394986, 360582377601524924, 360582377764455771, 360582378569614118, 360582379374914551]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360612033863917470, 360612043429328660⟩, ⟨(-1169644237580157265), (-1169389313124536957)⟩, true⟩

def words02 : List Nat := [360582380651874511, 360582381642420859, 360582382183238813, 360582382724099232, 360582382935160384, 360582383468012173, 360582384478067042, 360582385488172815, 360582386078709789, 360582386831394940]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360635534162017236, 360635543732472139⟩, ⟨(-2096600221215788555), (-2096345097861777919)⟩, true⟩

def words03 : List Nat := [360582387390415588, 360582387949557149, 360582388935749376, 360582389282404985, 360582389282900321, 360582388992632109, 360582388910854607, 360582389617592065, 360582390965744711, 360582392313951773]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360660323414041692, 360660332989578442⟩, ⟨(-3074550390100431948), (-3074295066293836954)⟩, true⟩

def words04 : List Nat := [360582393340473188, 360582394533345296, 360582396367552694, 360582398201824690, 360582399500926975, 360582400771914529, 360582401719883777, 360582402667858460, 360582404089950298, 360582406065893521]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360586026338787414, 360586035919358084⟩, ⟨(-142955890746655699), (-142700368325872899)⟩, true⟩

def words05 : List Nat := [360582408682800249, 360582411299685704, 360582413595101147, 360582415251395570, 360582416545429665, 360582417839542780, 360582418910930928, 360582419497015039, 360582419589146760, 360582419681342680]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360640191732039295, 360640201317651339⟩, ⟨(-2280575820816934075), (-2280320099438802129)⟩, true⟩

def words06 : List Nat := [360582420414411997, 360582421468404526, 360582422517388141, 360582423566419547, 360582424068246218, 360582424585417321, 360582425549047315, 360582426512792330, 360582427815719188, 360582429279966994]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360590303595776794, 360590313186482415⟩, ⟨(-311160855091482483), (-310904932645473871)⟩, true⟩

def words07 : List Nat := [360582430323278401, 360582431366595256, 360582432391027228, 360582433900950397, 360582435242666851, 360582436584402030, 360582437605091567, 360582437987660380, 360582438187568754, 360582438387651447]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575636271859087, 360575645867592869⟩, ⟨267896634155310209, 268152755139089535⟩, true⟩

def words08 : List Nat := [360582438775992615, 360582438889255118, 360582438889735794, 360582438590725021, 360582438291642434, 360582437705246283, 360582437438869345, 360582437154103578, 360582436869293894, 360582436264025867]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360641298525597757, 360641308126374966⟩, ⟨(-2325594967169598441), (-2325338646996287841)⟩, true⟩

def words09 : List Nat := [360582436092511991, 360582435789286783, 360582435640740029, 360582436134352984, 360582436134845855, 360582436079195489, 360582436450812837, 360582437302152537, 360582438792985528, 360582440283864744]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk394
