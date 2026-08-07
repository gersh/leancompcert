import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk180

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360715317899898853, 360715319762693739⟩, ⟨(-2362669428894869844), (-2362646732627777372)⟩, true⟩

def state01 : KState := ⟨⟨360634371678105256, 360634373543053592⟩, ⟨(-905287610538544779), (-905264875498400113)⟩, true⟩

def words00 : List Nat := [360584078159008675, 360584084351461006, 360584088342317518, 360584092332759122, 360584094602992522, 360584098415700470, 360584102694823895, 360584106973514569, 360584108974493785, 360584111765501075]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 18000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 18000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360686912234484297, 360686914101597541⟩, ⟨(-1852159805101195420), (-1852137031060840728)⟩, true⟩

def words01 : List Nat := [360584113663266084, 360584115560884282, 360584120530319639, 360584122440748786, 360584122440959715, 360584121722575633, 360584122097657946, 360584126097896821, 360584131802189004, 360584137505900253]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 18010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 18000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360565311870759944, 360565313740050450⟩, ⟨339345155516146400, 339367968801997270⟩, true⟩

def words02 : List Nat := [360584141662414085, 360584142762024735, 360584145849504158, 360584148936707648, 360584149742607191, 360584149742836282, 360584147492863464, 360584143674957286, 360584139857432199, 360584136145419391]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 18020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 18000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360426854857288360, 360426856728740706⟩, ⟨2836498018552793453, 2836520870827351367⟩, true⟩

def words03 : List Nat := [360584135101714703, 360584133416646734, 360584131731736377, 360584128502849108, 360584123435073715, 360584117579646089, 360584111724799050, 360584106865881005, 360584100526430124, 360584091810272156]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 18030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 18000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360663946380173261, 360663948253787589⟩, ⟨(-1441841123006359870), (-1441818231718835206)⟩, true⟩

def words04 : List Nat := [360584083095027225, 360584077442341068, 360584073761296135, 360584073141891561, 360584072522538442, 360584069300887608, 360584066197131947, 360584066153958105, 360584069127138590, 360584073552567777]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 18040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 18000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360595244666340454, 360595246542142406⟩, ⟨(-201552767087563874), (-201529836302726022)⟩, true⟩

def words05 : List Nat := [360584075581982991, 360584077611197174, 360584079533636853, 360584083811034064, 360584086331700099, 360584088852124235, 360584089457465888, 360584089457695415, 360584087636212103, 360584088254323198]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 18050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 18000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360603307149755809, 360603309027717923⟩, ⟨(-347076359486894563), (-347053389678421153)⟩, true⟩

def words06 : List Nat := [360584091929174953, 360584095222903939, 360584096797522929, 360584098371990658, 360584099158907576, 360584101479283870, 360584102599040746, 360584103718714196, 360584103718919168, 360584104036866370]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 18060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 18000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360692546155450206, 360692548035579427⟩, ⟨(-1960394259929896341), (-1960371250950974625)⟩, true⟩

def words07 : List Nat := [360584106094223460, 360584108151421541, 360584109493497627, 360584110948015948, 360584110948227878, 360584109779167285, 360584110493196843, 360584114424283879, 360584120421904121, 360584126418912707]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 18070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 18000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608245648150958, 360608247530473811⟩, ⟨(-436510155841501358), (-436487107191267414)⟩, true⟩

def words08 : List Nat := [360584129779096684, 360584130102392607, 360584131018376033, 360584131934325845, 360584132066836213, 360584132067066088, 360584129163704865, 360584124722813697, 360584120282364763, 360584120223680861]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 18080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 18000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360490653057156911, 360490654941643787⟩, ⟨1691529884954917746, 1691552972763200932⟩, true⟩

def words09 : List Nat := [360584123608587320, 360584126993163467, 360584128277232932, 360584128277462948, 360584127507871029, 360584123883576561, 360584120259614376, 360584119680891332, 360584116070349823, 360584110906989821]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 18090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 18000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 18000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk180
