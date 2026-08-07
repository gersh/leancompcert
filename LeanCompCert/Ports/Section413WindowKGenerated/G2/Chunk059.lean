import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk059

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360950999461000827, 360950999640391511⟩, ⟨(-2247439647277304429), (-2247438929039655823)⟩, true⟩

def state01 : KState := ⟨⟨360819389228791226, 360819389408827224⟩, ⟨(-1471094360568450057), (-1471093638520198147)⟩, true⟩

def words00 : List Nat := [360570185054600709, 360570221927299694, 360570287351241219, 360570352753044009, 360570410414116100, 360570439716991733, 360570447371354013, 360570455023133642, 360570473395464314, 360570515506184660]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 5900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 5900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360474399070215428, 360474399250889989⟩, ⟨569656033531272084, 569656759356685624⟩, true⟩

def words01 : List Nat := [360570568876757127, 360570622229290371, 360570660261540104, 360570669987487768, 360570669987545840, 360570656078449424, 360570642914149192, 360570642914217454, 360570641311870112, 360570625054835376]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 5910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 5900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360681327976155842, 360681328157472313⟩, ⟨(-655390092019941319), (-655389362391262791)⟩, true⟩

def words02 : List Nat := [360570608803276935, 360570627960440920, 360570677116528043, 360570726256035196, 360570750893151471, 360570750893219368, 360570772097196582, 360570796844765427, 360570807185666662, 360570825820195082]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 5920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 5900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360630022265292583, 360630022447256473⟩, ⟨(-351013165820065529), (-351012432348968413)⟩, true⟩

def words03 : List Nat := [360570830304665024, 360570834787630116, 360570847062208189, 360570879037110675, 360570903460608447, 360570927875890778, 360570937728891280, 360570937728959292, 360570929445099090, 360570939391819852]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 5930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 5900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360495058095629832, 360495058278235809⟩, ⟨450132955304599669, 450133692592953181⟩, true⟩

def words04 : List Nat := [360570956638253551, 360570956638321598, 360570945814159870, 360570913654451386, 360570881505551113, 360570832050550458, 360570797173752329, 360570773099561198, 360570749033456746, 360570710999680003]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 5940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 5900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360592254760030646, 360592254943280438⟩, ⟨(-128737416217714891), (-128736675095398155)⟩, true⟩

def words05 : List Nat := [360570698287129156, 360570688665403979, 360570697473659365, 360570709990264854, 360570709990327731, 360570698535393113, 360570687084292562, 360570661677098573, 360570654829938784, 360570658453581496]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 5950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 5900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589525224883659, 360589525408784601⟩, ⟨(-113418046191059339), (-113417301184665583)⟩, true⟩

def words06 : List Nat := [360570658453642428, 360570647598861752, 360570636341516597, 360570638428657643, 360570638428715031, 360570633039194331, 360570618457037045, 360570582954826383, 360570547464498419, 360570530717579667]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 5960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 5900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360371712703984601, 360371712888531755⟩, ⟨1187743583554001292, 1187744332421541308⟩, true⟩

def words07 : List Nat := [360570532465623265, 360570534213093559, 360570534213155000, 360570514989683736, 360570484960910289, 360570446478810387, 360570408009566958, 360570384432071785, 360570365561553224, 360570332342113953]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 5970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 5900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360807319750895820, 360807319936090285⟩, ⟨(-1419163539083968915), (-1419162786342266673)⟩, true⟩

def words08 : List Nat := [360570299133767413, 360570302594026343, 360570326103784659, 360570349605700251, 360570349605765202, 360570348587177624, 360570351213540539, 360570366367696045, 360570397934960516, 360570437481351132]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 5980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 5900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360503747566744983, 360503747752594543⟩, ⟨401300223509623610, 401300980178629552⟩, true⟩

def words09 : List Nat := [360570462729673343, 360570487969578199, 360570520542715214, 360570570843390326, 360570602721166427, 360570634588322024, 360570652217527881, 360570652217596644, 360570642398320439, 360570631249290982]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 5990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 5900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 5900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk059
