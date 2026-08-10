import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk694A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk694B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk694A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk694B
