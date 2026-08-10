import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk546A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk546B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk546A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk546B
