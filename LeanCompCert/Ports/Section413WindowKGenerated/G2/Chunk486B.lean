import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk486A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk486B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk486A

def state06 : KState := ⟨⟨360561403542996384, 360561418364252036⟩, ⟨1006915936521735381, 1007403273232273145⟩, true⟩

def words05 : List Nat := [360582120098244816, 360582120325622647, 360582120617694342, 360582121218997029, 360582121609016084, 360582121999128192, 360582122056456467, 360582122057126487, 360582121692229602, 360582121267524381]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577250063656879, 360577264891216747⟩, ⟨235733811721045175, 236221455226767065⟩, true⟩

def words06 : List Nat := [360582120842614452, 360582120838781376, 360582120616555673, 360582120180299497, 360582119743935745, 360582119202529956, 360582118874052275, 360582118794159718, 360582118714196303, 360582118424301333]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604720391019418, 360604735224916402⟩, ⟨(-1101575585030140629), (-1101087633066458597)⟩, true⟩

def words07 : List Nat := [360582118325132738, 360582118037683519, 360582117882575277, 360582117883245517, 360582117594512366, 360582116863980186, 360582116133349405, 360582115867632630, 360582116332828495, 360582116798157165]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598848107818227, 360598862948100369⟩, ⟨(-815870856737029112), (-815382593912405330)⟩, true⟩

def words08 : List Nat := [360582117042161679, 360582117042832042, 360582117256107291, 360582117517917814, 360582117518491186, 360582117429313311, 360582117280371310, 360582116921657573, 360582116562828367, 360582116884271070]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360541324133864828, 360541338980469662⟩, ⟨1985311049137330651, 1985799619845405803⟩, true⟩

def words09 : List Nat := [360582117201388953, 360582117518633126, 360582117626030525, 360582117626701136, 360582117452852466, 360582117174194937, 360582116895357121, 360582116502798203, 360582115989977114, 360582115153361765]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk486B
