import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk217A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk217B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk217A

def state06 : KState := ⟨⟨360557653461651879, 360557656230579103⟩, ⟨486495717185125288, 486536485313734320⟩, true⟩

def words05 : List Nat := [360580024764767098, 360580025328610927, 360580025328863297, 360580024837168068, 360580023023834389, 360580020127093599, 360580017230531841, 360580016471101723, 360580016471351879, 360580015444058595]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 21750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 21700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360616202832918095, 360616205604499767⟩, ⟨(-787855765389206342), (-787814939486596378)⟩, true⟩

def words06 : List Nat := [360580014780149024, 360580016538144329, 360580018228693276, 360580019919136638, 360580019919395508, 360580019795674139, 360580017572034440, 360580017451789252, 360580017504089910, 360580019166601343]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 21760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 21700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360565050660214730, 360565053434474712⟩, ⟨326099697436552070, 326140581658798180⟩, true⟩

def words07 : List Nat := [360580019330818703, 360580019495049291, 360580021761176859, 360580025344428090, 360580027626847272, 360580029909101261, 360580030222066824, 360580030222347991, 360580028436751105, 360580027749518734]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 21770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 21700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360557478583973015, 360557481360878106⟩, ⟨490869655626894986, 490910597473297324⟩, true⟩

def words08 : List Nat := [360580027320614403, 360580027320895617, 360580025481362137, 360580022379262670, 360580019277397457, 360580015643072599, 360580013067059603, 360580012590287079, 360580012113528836, 360580010530105885]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 21780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 21700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586361793817030, 360586364573381337⟩, ⟨(-139110488948777839), (-139069489144890513)⟩, true⟩

def words09 : List Nat := [360580009496463969, 360580007374859624, 360580005253368805, 360580002875754308, 360579999848720754, 360579995014539276, 360579990180747736, 360579986750466425, 360579985238725356, 360579985531633487]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 21790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 21700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 21700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk217B
