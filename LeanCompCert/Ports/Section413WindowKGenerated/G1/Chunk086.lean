import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk086

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362434817986664856, 362434818904445311⟩, ⟨406771069797325111, 406776414363326579⟩, true⟩

def state01 : KState := ⟨⟨362416736122810816, 362416737042836499⟩, ⟨562010187010268978, 562015550896681866⟩, true⟩

def words00 : List Nat := [371282112988384629, 371282106110988163, 371282091887266036, 371282083239918139, 371282074594458629, 371282070141429336, 371282052916198836, 371282034742250705, 371282016572421293, 371282011787423803]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 8600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 8600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362308795407904324, 362308796330165402⟩, ⟨1492445694126529502, 1492451077271396798⟩, true⟩

def words01 : List Nat := [371282008232357829, 371282012256845880, 371282012883766379, 371282012884015333, 371281998580707214, 371281988465224813, 371281978351963537, 371281973808049060, 371281954593871922, 371281934506182966]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 8610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 8600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362464857315221437, 362464858239712166⟩, ⟨146610971254583957, 146616373630415851⟩, true⟩

def words02 : List Nat := [371281914423047124, 371281904300286062, 371281887609789253, 371281884257201583, 371281880905305346, 371281874349132775, 371281854278947750, 371281847540186636, 371281847390512383, 371281847390770152]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 8620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 8600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362470534431727097, 362470535358497228⟩, ⟨97533086310673277, 97538508368883309⟩, true⟩

def words03 : List Nat := [371281845422574325, 371281840799527014, 371281841747978163, 371281841748252571, 371281840581286749, 371281839590471485, 371281838599803746, 371281837736335102, 371281825844161260, 371281824537706590]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 8630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 8600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362463324332741857, 362463325261735125⟩, ⟨160080214427837075, 160085655705521399⟩, true⟩

def words04 : List Nat := [371281835213999356, 371281835214249216, 371281833116919581, 371281829542784989, 371281825969388948, 371281822776435748, 371281820783798266, 371281826424362564, 371281832273696608, 371281832273955417]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 8640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 8600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362509402061086133, 362509402992340785⟩, ⟨(-238575355515396733), (-238569894665190521)⟩, true⟩

def words05 : List Nat := [371281837711758093, 371281845287231536, 371281861269332967, 371281861269583123, 371281859545718035, 371281855337037336, 371281853672014085, 371281853672293340, 371281854505380816, 371281857686410155]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 8650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 8600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362524451242738432, 362524452176250291⟩, ⟨(-369363198091470733), (-369357717682196595)⟩, true⟩

def words06 : List Nat := [371281860993282830, 371281860993533273, 371281851119294180, 371281852791576580, 371281858598920140, 371281858599174840, 371281853420732794, 371281848000225445, 371281850363083009, 371281855276506064]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 8660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 8600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362341908253057233, 362341909188830729⟩, ⟨1214435777992825224, 1214441278022017974⟩, true⟩

def words07 : List Nat := [371281863663537151, 371281872048737388, 371281877213633129, 371281877213883755, 371281864756579553, 371281855851725174, 371281851227566916, 371281851227817586, 371281837898995756, 371281821778464603]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 8670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 8600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362428817116777035, 362428818054794850⟩, ⟨459924962100264533, 459930481621744913⟩, true⟩

def words08 : List Nat := [371281805661530087, 371281802719205683, 371281793190015176, 371281793258407946, 371281793258603913, 371281791645884767, 371281775158782621, 371281760539100925, 371281745922652530, 371281744462346260]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 8680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 8600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477082184992111, 362477083125293802⟩, ⟨40473513272409603, 40479052652278603⟩, true⟩

def words09 : List Nat := [371281738372739369, 371281732399509951, 371281733596622247, 371281736651037159, 371281741435451698, 371281746218863431, 371281750089336269, 371281750089587613, 371281736424520607, 371281735889966478]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 8690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 8600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 8600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk086
