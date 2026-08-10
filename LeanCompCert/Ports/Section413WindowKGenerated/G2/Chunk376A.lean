import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk376A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk376A
