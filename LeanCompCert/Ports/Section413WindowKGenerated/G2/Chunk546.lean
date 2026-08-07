import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk546

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360558472951369322, 360558491787846421⟩, ⟨1267973740849897930, 1268668630251682594⟩, true⟩

def state01 : KState := ⟨⟨360554462209683707, 360554481053299596⟩, ⟨1487008508849037103, 1487703788064453079⟩, true⟩

def words00 : List Nat := [360581727052104227, 360581726962149668, 360581726719311158, 360581726307926775, 360581725896426602, 360581725340740151, 360581724985476800, 360581724513324612, 360581724041106982, 360581723385987098]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360601755556671282, 360601774407446595⟩, ⟨(-1095975206021996198), (-1095279535794732596)⟩, true⟩

def words01 : List Nat := [360581722887757306, 360581722626504833, 360581722365033789, 360581722203333873, 360581722127905614, 360581721716540812, 360581721305045733, 360581721319469509, 360581721687221327, 360581722055131648]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360610955890414238, 360610974748437620⟩, ⟨(-1598743006991416657), (-1598046940839640509)⟩, true⟩

def words02 : List Nat := [360581722123040707, 360581722123800301, 360581722201836278, 360581722408661541, 360581722409299736, 360581722489073997, 360581722489750228, 360581722402370621, 360581722561204151, 360581723097528070]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579970166086842, 360579989031252919⟩, ⟨94262280281311687, 94958736675087247⟩, true⟩

def words03 : List Nat := [360581723968074172, 360581724838733836, 360581725541706888, 360581726025574997, 360581726261477665, 360581726497562367, 360581726784066447, 360581726959404421, 360581726960090216, 360581726929069081]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360608749722286326, 360608768594628916⟩, ⟨(-1478300931095231068), (-1477604082541797678)⟩, true⟩

def words04 : List Nat := [360581727109282674, 360581727579619548, 360581728280340063, 360581728981181866, 360581729397159167, 360581729574890447, 360581730086750917, 360581730598830790, 360581731007702234, 360581731503220858]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360573575790640538, 360573594670210707⟩, ⟨444165054447443591, 444862298025214017⟩, true⟩

def words05 : List Nat := [360581731831190673, 360581732159235023, 360581732491712001, 360581732992558930, 360581733295751798, 360581733599069139, 360581733733989198, 360581733734748678, 360581733535734922, 360581733387701107]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 54650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 54600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580976327636160, 360580995214369550⟩, ⟨39496156813503427, 40193791968050037⟩, true⟩

def words06 : List Nat := [360581733316472053, 360581733317231617, 360581733143663074, 360581732699016278, 360581732254265387, 360581731586662183, 360581731086625792, 360581730920793558, 360581730754884410, 360581730421831926]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 54660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 54600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599568717990164, 360599587611886978⟩, ⟨(-977090081763172033), (-976392054948449267)⟩, true⟩

def words07 : List Nat := [360581730551525819, 360581730694886687, 360581731171975413, 360581731315539248, 360581731316247751, 360581731175568901, 360581731034760500, 360581730816220290, 360581731136064922, 360581731463408559]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 54670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 54600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360589776236824841, 360589795137955101⟩, ⟨(-441712228760294961), (-441013806385338427)⟩, true⟩

def words08 : List Nat := [360581731538194660, 360581731538956143, 360581731664214411, 360581731855683873, 360581731962601772, 360581731963362097, 360581731883604560, 360581731636767402, 360581731389795370, 360581731401574612]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 54680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 54600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574311974809152, 360574330883104885⟩, ⟨404060339147320438, 404759153437001320⟩, true⟩

def words09 : List Nat := [360581731405868313, 360581731410299032, 360581731410982528, 360581731201022329, 360581731050353262, 360581730815672616, 360581730603305317, 360581730635811815, 360581730636488910, 360581730501997701]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 54690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 54600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 54600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk546
