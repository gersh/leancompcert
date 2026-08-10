import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk872A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk872B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk872A

def state06 : KState := ⟨⟨360583194620420335, 360583244550874038⟩, ⟨(-96885280731811832), (-93943023623396014)⟩, true⟩

def words05 : List Nat := [360582169225573556, 360582169070211545, 360582168914474766, 360582168890167178, 360582168734541113, 360582168456311291, 360582168177841065, 360582168030922042, 360582167962092340, 360582167975730235]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 87250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 87200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360560035657005023, 360560085599440999⟩, ⟨1924055452523698529, 1926998755264214287⟩, true⟩

def words06 : List Nat := [360582167976853533, 360582167877555822, 360582167824044945, 360582167791337233, 360582167758283551, 360582167668646718, 360582167447654214, 360582167146808186, 360582166845751254, 360582166483539363]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 87260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 87200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561579167166645, 360561629121426078⟩, ⟨1789381663977195341, 1792325998611044389⟩, true⟩

def words07 : List Nat := [360582166231539716, 360582166091435036, 360582165951206977, 360582165745533305, 360582165519769734, 360582165260302799, 360582165000448610, 360582164871957247, 360582164712863727, 360582164478880376]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 87270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 87200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586302232093756, 360586352198232617⟩, ⟨(-368602613022749649), (-365657241495897605)⟩, true⟩

def words08 : List Nat := [360582164244617252, 360582164141853980, 360582164123772338, 360582164065015743, 360582164006172396, 360582163811083910, 360582163558935681, 360582163414979809, 360582163270658558, 360582163252734274]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 87280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 87200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578204780769991, 360578254758883742⟩, ⟨338269268321735217, 341215685195686869⟩, true⟩

def words09 : List Nat := [360582163253865721, 360582163220461275, 360582163283226403, 360582163447062470, 360582163503918363, 360582163560979595, 360582163562118665, 360582163518661175, 360582163343846958, 360582163300524014]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 87290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 87200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 87200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk872B
