import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk077

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360781841608384932, 360781841922378513⟩, ⟨(-1539770500920104600), (-1539768861507806856)⟩, true⟩

def state01 : KState := ⟨⟨360524633069666869, 360524633384523109⟩, ⟨441163511470391993, 441165157529514197⟩, true⟩

def words00 : List Nat := [360581911679201977, 360581911679292654, 360581922646766731, 360581936505719036, 360581940227086473, 360581940227177207, 360581927292663524, 360581901210270186, 360581875134626685, 360581853249312930]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 7700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 7700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360532078304399304, 360532078620110651⟩, ⟨383857464993899711, 383859117650212401⟩, true⟩

def words01 : List Nat := [360581845828836530, 360581840569324106, 360581835311166291, 360581821448940191, 360581816409605294, 360581806912595555, 360581804620831464, 360581807745165536, 360581807745246588, 360581801303744099]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 7710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 7700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360756877800698910, 360756878117270378⟩, ⟨(-1352748062242074643), (-1352746402941429537)⟩, true⟩

def words02 : List Nat := [360581794863891097, 360581794665190179, 360581818158272319, 360581841645289374, 360581850454032361, 360581850454123365, 360581851565328782, 360581860449610319, 360581878582513711, 360581901218687863]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 7720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 7700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360521897302350976, 360521897619790348⟩, ⟨464526995298062823, 464528661311884905⟩, true⟩

def words03 : List Nat := [360581915331780957, 360581929441233217, 360581936174795612, 360581951419105549, 360581951419183733, 360581950448947029, 360581949478951194, 360581940009791013, 360581921997681853, 360581914242698861]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 7730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 7700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360630942826623319, 360630943144923720⟩, ⟨(-379658337836934300), (-379656665154502564)⟩, true⟩

def words04 : List Nat := [360581915331778967, 360581926356341885, 360581926675996254, 360581926995578596, 360581926995655148, 360581927323984604, 360581941399366443, 360581955471133168, 360581955471216725, 360581961508340763]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 7740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 7700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360878915225246182, 360878915544409417⟩, ⟨(-2303318561859171774), (-2303316882485466244)⟩, true⟩

def words05 : List Nat := [360581974489268871, 360581987466875057, 360582016978463599, 360582030040016534, 360582030040101335, 360582026638815788, 360582036360951744, 360582058103528434, 360582096358427485, 360582134603488729]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 7750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 7700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360725148576529593, 360725148896565875⟩, ⟨(-1110684977682758594), (-1110683291529820042)⟩, true⟩

def words06 : List Nat := [360582162694401593, 360582174360961925, 360582185491730882, 360582196619658092, 360582203416970252, 360582208554043130, 360582208554125492, 360582205315685419, 360582203813895021, 360582222208684030]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 7760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 7700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360412618317772557, 360412618638672429⟩, ⟨1320120502579049810, 1320122195446552166⟩, true⟩

def words07 : List Nat := [360582247122963430, 360582272030849692, 360582288510820381, 360582306393454050, 360582319426604915, 360582332456428869, 360582335385206660, 360582335385298441, 360582321967468946, 360582300154796665]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 7770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 7700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360716476167392092, 360716476489158983⟩, ⟨(-1045747193746921075), (-1045745494129685145)⟩, true⟩

def words08 : List Nat := [360582278347710630, 360582265265560574, 360582265159576741, 360582269766428038, 360582269766513403, 360582260248373281, 360582246571283076, 360582237072113470, 360582234448738994, 360582251679233469]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 7780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 7700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360720273414800749, 360720273737444175⟩, ⟨(-1075360722324312369), (-1075359015874486775)⟩, true⟩

def words09 : List Nat := [360582255923492596, 360582260166671151, 360582280763949753, 360582309856515022, 360582334662858342, 360582359462853519, 360582373958402672, 360582389519303371, 360582407196842309, 360582424869879186]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 7790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 7700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 7700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk077
