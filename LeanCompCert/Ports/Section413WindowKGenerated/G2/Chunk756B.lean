import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk756A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk756B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk756A

def state06 : KState := ⟨⟨360596699936695995, 360596737059493651⟩, ⟨(-1101688981006605385), (-1099791924420845721)⟩, true⟩

def words05 : List Nat := [360582200954091579, 360582200800136579, 360582200665477655, 360582200771977303, 360582200833981436, 360582200896178655, 360582200897139005, 360582200889523000, 360582201082519329, 360582201275874338]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360586674012153056, 360586711145111155⟩, ⟨(-343142486324818402), (-341244660948713502)⟩, true⟩

def words06 : List Nat := [360582201562814251, 360582201675492208, 360582201676478482, 360582201654487865, 360582201632322731, 360582201527423180, 360582201550657429, 360582201592526865, 360582201593493854, 360582201562035093]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592469321056914, 360592506464185947⟩, ⟨(-781736557816646198), (-779837962754203570)⟩, true⟩

def words07 : List Nat := [360582201729036429, 360582201896360063, 360582202115312944, 360582202201864448, 360582202202859948, 360582202139565279, 360582202076083080, 360582201951443195, 360582202050234930, 360582202187514733]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360606209596590930, 360606246749991836⟩, ⟨(-1821798295890179506), (-1819898923403271568)⟩, true⟩

def words08 : List Nat := [360582202238168184, 360582202239246374, 360582202257114860, 360582202354016007, 360582202406460100, 360582202485762884, 360582202486723564, 360582202478662954, 360582202635611639, 360582202954515449]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360575494263248518, 360575531426815655⟩, ⟨503154748026154994, 505054890046717104⟩, true⟩

def words09 : List Nat := [360582203181471986, 360582203408607844, 360582203526463240, 360582203527541497, 360582203471042637, 360582203370716794, 360582203285855146, 360582203307972406, 360582203308946872, 360582203221928558]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk756B
