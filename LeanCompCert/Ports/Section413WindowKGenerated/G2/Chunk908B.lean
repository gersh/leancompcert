import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk908A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk908B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk908A

def state06 : KState := ⟨⟨360581886787108312, 360581941092151769⟩, ⟨1963927788254317, 5295842859022207⟩, true⟩

def words05 : List Nat := [360581999765184152, 360581999848742939, 360581999929238998, 360581999930551084, 360581999890222744, 360581999748326810, 360581999606188000, 360581999454592600, 360581999377147309, 360581999377897521]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 90850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 90800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360570056481147126, 360570110798673827⟩, ⟨1076840918018280131, 1080173967379826237⟩, true⟩

def words06 : List Nat := [360581999378425963, 360581999310698905, 360581999146747630, 360581999104176388, 360581999061247515, 360581998947851094, 360581998713396371, 360581998385955115, 360581998058269641, 360581997823735782]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 90860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 90800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360550006592625196, 360550060922500003⟩, ⟨2898910671461612481, 2902244842958948867⟩, true⟩

def words07 : List Nat := [360581997693991783, 360581997580576896, 360581997467033298, 360581997275397251, 360581997086481833, 360581996864965926, 360581996643071654, 360581996474550409, 360581996184985978, 360581995834944534]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 90870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 90800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571789779210038, 360571844121495941⟩, ⟨919107221012495771, 922442520488423721⟩, true⟩

def words08 : List Nat := [360581995484631325, 360581995132035051, 360581994887780404, 360581994680314294, 360581994472751060, 360581994163917634, 360581993790077607, 360581993537563009, 360581993284643301, 360581993120511107]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 90880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 90800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554846570904506, 360554900925702350⟩, ⟨2459166772405965471, 2462503209151730857⟩, true⟩

def words09 : List Nat := [360581993010030330, 360581992839274509, 360581992668277048, 360581992516158636, 360581992424465233, 360581992243015732, 360581992061416516, 360581991804343909, 360581991466539641, 360581991170027452]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 90890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 90800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 90800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk908B
