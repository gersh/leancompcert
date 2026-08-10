import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk801A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk801B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk801A

def state06 : KState := ⟨⟨360597971269546637, 360598013128944641⟩, ⟨(-1272569627276887292), (-1270303432606534992)⟩, true⟩

def words05 : List Nat := [360582164123032105, 360582164298025635, 360582164628221999, 360582165053886568, 360582165333939458, 360582165614168851, 360582165745026137, 360582165830303907, 360582166028926727, 360582166227925361]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601415616650076, 360601457486835719⟩, ⟨(-1548727509886550125), (-1546460450423496325)⟩, true⟩

def words06 : List Nat := [360582166495589059, 360582166647970888, 360582166722763788, 360582166797689403, 360582166833580699, 360582166958476857, 360582167238393227, 360582167518529883, 360582167720768999, 360582167962563558]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606057090874890, 360606098971903892⟩, ⟨(-1920913140063705447), (-1918645211237136415)⟩, true⟩

def words07 : List Nat := [360582168139405459, 360582168316574171, 360582168648728257, 360582168825872239, 360582168871973297, 360582168918160908, 360582169119457873, 360582169446947397, 360582169746328760, 360582170045958380]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583538618381567, 360583580510339713⟩, ⟨(-115341410907225506), (-113072605730449804)⟩, true⟩

def words08 : List Nat := [360582170247084916, 360582170345440889, 360582170574087573, 360582170803071165, 360582170903658578, 360582170904805340, 360582170850264413, 360582170718140980, 360582170585804144, 360582170469241206]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360551969133875153, 360552011036641409⟩, ⟨2416481774157100310, 2418751446090001178⟩, true⟩

def words09 : List Nat := [360582170643028957, 360582170817051973, 360582170913234693, 360582170914381636, 360582170898503300, 360582170815499626, 360582170732166052, 360582170647237294, 360582170407091865, 360582170032228567]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk801B
