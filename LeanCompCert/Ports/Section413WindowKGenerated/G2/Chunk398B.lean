import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk398A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk398B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk398A

def state06 : KState := ⟨⟨360640655400219200, 360640665183984070⟩, ⟨(-2317514174852461625), (-2317250593690057173)⟩, true⟩

def words05 : List Nat := [360582524262767662, 360582525359376429, 360582526551814734, 360582527117631718, 360582527143386934, 360582527169183351, 360582527822964510, 360582528988058906, 360582530447005659, 360582531906000827]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360631067453358548, 360631077242265163⟩, ⟨(-1935496589960811630), (-1935232803823296526)⟩, true⟩

def words06 : List Nat := [360582532969945715, 360582533765100981, 360582535188013775, 360582536611017313, 360582537430620897, 360582537884168118, 360582537937259234, 360582537990406674, 360582538671194419, 360582539889205965]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569606175842951, 360569615969839596⟩, ⟨515331640294490641, 515595629397236075⟩, true⟩

def words07 : List Nat := [360582541291599858, 360582542694034086, 360582543782024627, 360582544244081967, 360582544244537902, 360582544222428704, 360582544804933762, 360582544969749160, 360582544970243492, 360582544646604823]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360671889464205561, 360671899263301218⟩, ⟨(-3564261202720531730), (-3563997010244282746)⟩, true⟩

def words08 : List Nat := [360582544322861082, 360582544722637730, 360582545800689691, 360582546878793644, 360582547417979777, 360582548379542120, 360582549968150792, 360582551556843522, 360582553637015304, 360582555877318308]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360616966407269879, 360616976211517956⟩, ⟨(-1373076421446836082), (-1372812023416297016)⟩, true⟩

def words09 : List Nat := [360582557803400355, 360582559729444873, 360582561438183552, 360582563515775898, 360582565307335054, 360582567098892481, 360582568377913459, 360582569031739694, 360582569894513085, 360582570757433691]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk398B
