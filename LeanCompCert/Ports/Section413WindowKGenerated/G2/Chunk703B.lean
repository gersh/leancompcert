import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk703A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk703B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk703A

def state06 : KState := ⟨⟨360545817642892357, 360545849562597195⟩, ⟨2575780393886435195, 2577297393574873213⟩, true⟩

def words05 : List Nat := [360582481124421505, 360582481241750241, 360582481257562511, 360582481258560081, 360582481168249011, 360582481027547471, 360582480886561423, 360582480636293867, 360582480232745729, 360582479713159658]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 70350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 70300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360558269005814112, 360558300934926690⟩, ⟨1699667794040903042, 1701185455704950538⟩, true⟩

def words06 : List Nat := [360582479193362718, 360582478818275324, 360582478544822630, 360582478340832392, 360582478136753028, 360582477760614365, 360582477232204543, 360582476736037844, 360582476239596657, 360582475802849171]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 70360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 70300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581175409742444, 360581207348372719⟩, ⟨87558295537945580, 89076627007132786⟩, true⟩

def words07 : List Nat := [360582475460226978, 360582474963839708, 360582474467275607, 360582474172449851, 360582474007232822, 360582473783893086, 360582473560449054, 360582473236342845, 360582473017761183, 360582473000930366]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 70370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 70300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581523197449334, 360581555145461936⟩, ⟨63105640352059437, 64624632197103673⟩, true⟩

def words08 : List Nat := [360582473167163777, 360582473292781305, 360582473293670589, 360582473292290493, 360582473290762122, 360582473149486926, 360582473204872181, 360582473301064230, 360582473301968187, 360582473239398534]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 70380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 70300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586086027042437, 360586117984485838⟩, ⟨(-258045984808807132), (-256526329083340296)⟩, true⟩

def words09 : List Nat := [360582473345002883, 360582473463958038, 360582473783924826, 360582473967561395, 360582473985723681, 360582474003956524, 360582474004765432, 360582474090963275, 360582474143543644, 360582474196342441]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 70390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 70300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 70300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk703B
