import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk694

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468955924348990, 362469027354841519⟩, ⟨1132605638025039011, 1135953633109477979⟩, true⟩

def state01 : KState := ⟨⟨362482193390507829, 362482264842247301⟩, ⟨213910695708049218, 217260165439373452⟩, true⟩

def words00 : List Nat := [371285395328571785, 371285395302514905, 371285395272831188, 371285395363318441, 371285395407349428, 371285395409723860, 371285395177064668, 371285395041500434, 371285394938684057, 371285394941158689]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 69400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 69400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476900655191250, 362476972128547790⟩, ⟨581346456812976596, 584697427093674612⟩, true⟩

def words01 : List Nat := [371285394897843329, 371285394826982570, 371285394840773143, 371285394843393765, 371285394907555844, 371285394973205235, 371285395037041341, 371285395039416797, 371285394854656848, 371285394736255853]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 69410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 69400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474933581316475, 362475005075829973⟩, ⟨717899100522488250, 721251539627332450⟩, true⟩

def words02 : List Nat := [371285394616551127, 371285394605242472, 371285394337687709, 371285394074676840, 371285393810734288, 371285393611822981, 371285393367667270, 371285393331485376, 371285393294516742, 371285393258742653]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 69420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 69400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490800185675887, 362490871701715460⟩, ⟨(-383812239227045212), (-380458305461196384)⟩, true⟩

def words03 : List Nat := [371285393168109282, 371285393228365088, 371285393338381109, 371285393340756907, 371285393192155979, 371285393010807849, 371285392828521847, 371285392796239485, 371285392748710812, 371285392830364800]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 69430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 69400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362467789381942470, 362467860919400394⟩, ⟨1214116918220701994, 1217472339387442882⟩, true⟩

def words04 : List Nat := [371285392914565266, 371285392916941260, 371285392724825182, 371285392600373140, 371285392474755452, 371285392355814546, 371285392038377290, 371285391678176342, 371285391316998439, 371285391118671632]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 69440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 69400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362471449871331948, 362471521430156655⟩, ⟨959953379894161622, 963310285093303910⟩, true⟩

def words05 : List Nat := [371285390867872215, 371285390812638747, 371285390756642256, 371285390700977744, 371285390539596367, 371285390418174047, 371285390378043672, 371285390380420099, 371285390188718550, 371285389991704212]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 69450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 69400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483182808359338, 362483254388472172⟩, ⟨144942064563989563, 148300448546100329⟩, true⟩

def words06 : List Nat := [371285389793684444, 371285389684044383, 371285389501158319, 371285389514919811, 371285389516771067, 371285389468326641, 371285389182364700, 371285389104453331, 371285389126886207, 371285389129346595]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 69460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 69400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477802443866343, 362477874045672052⟩, ⟨518798362994860411, 522158254089510063⟩, true⟩

def words07 : List Nat := [371285389100414498, 371285389076867434, 371285389232891093, 371285389312386469, 371285389397685529, 371285389483857571, 371285389569711738, 371285389572088835, 371285389381904360, 371285389276732638]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 69470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 69400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470968365413901, 362471039988415175⟩, ⟨993730858973107100, 997092222846572176⟩, true⟩

def words08 : List Nat := [371285389268735942, 371285389271155322, 371285389203908509, 371285389118426913, 371285389032064241, 371285388986439073, 371285388844099340, 371285388810167999, 371285388775450280, 371285388703666961]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 69480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 69400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362503012356938866, 362503084001411913⟩, ⟨(-1233176041546534961), (-1229813185494441971)⟩, true⟩

def words09 : List Nat := [371285388498974093, 371285388501971026, 371285388710410201, 371285388712787883, 371285388645687179, 371285388542184987, 371285388538117098, 371285388588789016, 371285388845011790, 371285389102266657]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 69490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 69400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 69400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk694
