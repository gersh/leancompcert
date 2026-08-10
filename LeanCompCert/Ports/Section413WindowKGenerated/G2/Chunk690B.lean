import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk690A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk690B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk690A

def state06 : KState := ⟨⟨360576934448598414, 360576965154125439⟩, ⟨399257091605448536, 400689448356770726⟩, true⟩

def words05 : List Nat := [360582768986682945, 360582768648122481, 360582768309384759, 360582768144175904, 360582768122501570, 360582767954817229, 360582767787034787, 360582767514044734, 360582767285222215, 360582767202320585]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 69050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 69000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360589264685909505, 360589295400651584⟩, ⟨(-452285646550060661), (-450852653361481471)⟩, true⟩

def words06 : List Nat := [360582767244286395, 360582767376924342, 360582767404742258, 360582767432665955, 360582767433485483, 360582767395088202, 360582767638965940, 360582767883024365, 360582767925289997, 360582768020805318]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 69060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 69000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360608287731043020, 360608318455003860⟩, ⟨(-1766354829915290871), (-1764921199941751097)⟩, true⟩

def words07 : List Nat := [360582768170443662, 360582768320362104, 360582768679132838, 360582768828704976, 360582768829615849, 360582768799331016, 360582768887089626, 360582769137195117, 360582769507836900, 360582769878695733]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 69070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 69000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587567323750969, 360587598057030519⟩, ⟨(-335011836366370069), (-333577562612163843)⟩, true⟩

def words08 : List Nat := [360582770144759448, 360582770351396360, 360582770505797132, 360582770660478601, 360582770709667374, 360582770710644758, 360582770550572462, 360582770286005856, 360582770021257382, 360582769967082304]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 69080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 69000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360539863979662648, 360539894722140102⟩, ⟨2961106704226530104, 2962541613510947878⟩, true⟩

def words09 : List Nat := [360582770061779701, 360582770156657430, 360582770157537467, 360582770144225447, 360582769968644491, 360582769679011804, 360582769389114688, 360582769095298543, 360582768592145601, 360582767972697424]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 69090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 69000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 69000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk690B
