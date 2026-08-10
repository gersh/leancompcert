import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk531A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk531B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk531A

def state06 : KState := ⟨⟨360574578101530805, 360574595918826112⟩, ⟨390316929514127951, 390956901885616399⟩, true⟩

def words05 : List Nat := [360581950296622058, 360581950182522319, 360581950118448880, 360581950346246618, 360581950485236804, 360581950624342137, 360581950625002534, 360581950507881974, 360581950399858542, 360581950262352930]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 53150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 53100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360579533242555641, 360579551066788101⟩, ⟨126857372460104105, 127497713645555635⟩, true⟩

def words06 : List Nat := [360581950339337010, 360581950407489823, 360581950408157622, 360581950209123094, 360581950009987131, 360581949550029790, 360581949267646073, 360581949250827493, 360581949233929359, 360581948992566652]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 53160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 53100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360613930424727098, 360613948255927246⟩, ⟨(-1702134667987236894), (-1701493956295409970)⟩, true⟩

def words07 : List Nat := [360581949255909550, 360581949564577154, 360581950225923928, 360581950833374226, 360581951140256688, 360581951447187469, 360581951962496888, 360581952655612461, 360581953257866249, 360581953860254066]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 53170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 53100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608574923942419, 360608592762167962⟩, ⟨(-1417535767488061513), (-1416894682151171655)⟩, true⟩

def words08 : List Nat := [360581954242273032, 360581954271814937, 360581954406797036, 360581954541987520, 360581954542608760, 360581954475997507, 360581954476654378, 360581954332291692, 360581954395419772, 360581954897075162]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 53180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 53100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360573398116410410, 360573415961595366⟩, ⟨453738322802005041, 454379778343412953⟩, true⟩

def words09 : List Nat := [360581955623154117, 360581956349347033, 360581956748260785, 360581956794801380, 360581956795418660, 360581956753619777, 360581957021568863, 360581957093976751, 360581957094640874, 360581956934872498]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 53190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 53100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 53100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk531B
