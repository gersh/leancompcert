import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk376

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360558606338877589, 360558615003373134⟩, ⟨861228528046598172, 861448746731664448⟩, true⟩

def state01 : KState := ⟨⟨360572429911398835, 360572438580679136⟩, ⟨341486387598782965, 341706786214724369⟩, true⟩

def words00 : List Nat := [360581525265392154, 360581525005578281, 360581525470291611, 360581525935087109, 360581525935555159, 360581525759756308, 360581524879123947, 360581524705427201, 360581524531595994, 360581524110756635]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587418354674617, 360587427028793220⟩, ⟨(-222423381269776425), (-222202800661683721)⟩, true⟩

def words01 : List Nat := [360581523869655054, 360581523104653441, 360581522339595863, 360581521950483704, 360581521916029323, 360581521700213754, 360581521484354283, 360581520912875134, 360581520521010135, 360581520678598869]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584793175097779, 360584801853987364⟩, ⟨(-123715171330257200), (-123494411213762000)⟩, true⟩

def words02 : List Nat := [360581521068214607, 360581521263080854, 360581521263532687, 360581521102915450, 360581520942232043, 360581520237576760, 360581520090946520, 360581520295361540, 360581520295817857, 360581520133830745]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360606809437787026, 360606818121473728⟩, ⟨(-952312812012703856), (-952091871357242042)⟩, true⟩

def words03 : List Nat := [360581520294249195, 360581520454814625, 360581521320887943, 360581521785005900, 360581521785475798, 360581521649268978, 360581521860191296, 360581522765410282, 360581523437862519, 360581524110385892]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360656689476625417, 360656698165142357⟩, ⟨(-2830209216320483733), (-2829988093830786715)⟩, true⟩

def words04 : List Nat := [360581524427954124, 360581524992039141, 360581526261274908, 360581527530591823, 360581528618909590, 360581529729320185, 360581530410606101, 360581531091909310, 360581532478140049, 360581534475098779]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360611722028197718, 360611730721501148⟩, ⟨(-1136946477505640622), (-1136725174780386260)⟩, true⟩

def words05 : List Nat := [360581536802161488, 360581539129197174, 360581540766770318, 360581541930287947, 360581542677236488, 360581543424283681, 360581544875909730, 360581546032264937, 360581546834222558, 360581547636219813]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360649028239057997, 360649036937150554⟩, ⟨(-2542059309533428144), (-2541837826425702210)⟩, true⟩

def words06 : List Nat := [360581548646928578, 360581550010929497, 360581552079231734, 360581554147524752, 360581555633418233, 360581556728814757, 360581557801657743, 360581558874585617, 360581560487821489, 360581562279551189]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360628466230672195, 360628474933603692⟩, ⟨(-1767341718231614719), (-1767120052818174503)⟩, true⟩

def words07 : List Nat := [360581563632066831, 360581564984567152, 360581566841090408, 360581569297900335, 360581571257645378, 360581573217365895, 360581574758115442, 360581575597365375, 360581576842450909, 360581578087638400]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600189386084825, 360600198093805541⟩, ⟨(-701810431235962443), (-701588585340546831)⟩, true⟩

def words08 : List Nat := [360581579304115481, 360581580035795000, 360581580342267089, 360581580648774062, 360581580775002221, 360581581446973662, 360581582254700319, 360581583062488171, 360581583378890154, 360581583873292938]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360646013825314421, 360646022537832246⟩, ⟨(-2429161456507029653), (-2428939429785238409)⟩, true⟩

def words09 : List Nat := [360581585070973847, 360581586268745662, 360581588169681502, 360581589615311819, 360581590385233651, 360581591155147772, 360581591719872906, 360581592726292189, 360581594435716829, 360581596145169313]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk376
