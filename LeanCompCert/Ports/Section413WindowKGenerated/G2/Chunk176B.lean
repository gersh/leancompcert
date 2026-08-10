import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk176A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk176B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk176A

def state06 : KState := ⟨⟨360709995754016726, 360709997543991387⟩, ⟨(-2223210711692675315), (-2223189313850624429)⟩, true⟩

def words05 : List Nat := [360584098174828220, 360584096468431019, 360584095310970673, 360584097546674201, 360584097546881950, 360584096656309335, 360584098070078684, 360584102005107727, 360584109134141762, 360584116262418961]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 17650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 17600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360672911298631621, 360672913090743217⟩, ⟨(-1568808684963218691), (-1568787249372414487)⟩, true⟩

def words06 : List Nat := [360584120685858489, 360584121928533343, 360584124215690686, 360584126502654222, 360584127962525142, 360584129382077863, 360584129382280239, 360584128712542251, 360584130563641163, 360584135588090713]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 17660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 17600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360487730810062302, 360487732604284481⟩, ⟨1704542296053078099, 1704563768948544155⟩, true⟩

def words07 : List Nat := [360584142377179276, 360584149165542371, 360584153948889079, 360584155555443215, 360584155555634350, 360584154734988971, 360584153914370121, 360584153562662249, 360584150035407071, 360584144582166186]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 17670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 17600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360604569079832433, 360604570876174363⟩, ⟨(-361374663850326767), (-361353153467360689)⟩, true⟩

def words08 : List Nat := [360584139129489976, 360584137108876839, 360584140540048418, 360584143970874830, 360584144590126259, 360584144590350777, 360584144039335230, 360584144477403074, 360584144477588153, 360584145057765717]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 17680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 17600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360517821360065615, 360517823158543683⟩, ⟨1173791171247875456, 1173812719430001500⟩, true⟩

def words09 : List Nat := [360584145057965580, 360584144619909199, 360584144635857343, 360584146730062753, 360584148003125360, 360584149276084553, 360584149276285020, 360584148226842908, 360584144008021059, 360584140261336339]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 17690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 17600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 17600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk176B
