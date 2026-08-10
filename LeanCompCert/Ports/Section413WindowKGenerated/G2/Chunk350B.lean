import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk350A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk350B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk350A

def state06 : KState := ⟨⟨360630811391237150, 360630818881574304⟩, ⟨(-1715401967128694739), (-1715224424299734887)⟩, true⟩

def words05 : List Nat := [360581892008789150, 360581892240493735, 360581893284687034, 360581894065904068, 360581894123490076, 360581894181112678, 360581894356750101, 360581894940369893, 360581896336184787, 360581897732026381]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 35050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 35000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360605308799704740, 360605316294525279⟩, ⟨(-821492875496924464), (-821315175458234596)⟩, true⟩

def words06 : List Nat := [360581898540583115, 360581898832844451, 360581899102001396, 360581899371278840, 360581899436863533, 360581899437333902, 360581898928631612, 360581898010198698, 360581897091725072, 360581897653042053]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 35060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 35000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360538937121197229, 360538944620445871⟩, ⟨1506680738646537834, 1506858594000999800⟩, true⟩

def words07 : List Nat := [360581898586779016, 360581899520551808, 360581900034402374, 360581900738854530, 360581900958967234, 360581901179191127, 360581901376671431, 360581901377141907, 360581900764489936, 360581899540457303]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 35070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 35000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360626817422906834, 360626824926595912⟩, ⟨(-1576607581541397117), (-1576429570394577227)⟩, true⟩

def words08 : List Nat := [360581898316388065, 360581897905577656, 360581898718958379, 360581899532391062, 360581899651301302, 360581899651772010, 360581899259418939, 360581899104004404, 360581899603494990, 360581900884237628]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 35080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 35000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360647982334374414, 360647989842553628⟩, ⟨(-2319558326483657552), (-2319380157756559846)⟩, true⟩

def words09 : List Nat := [360581901519386111, 360581902154539064, 360581903137857487, 360581904527932785, 360581905714834429, 360581906901745528, 360581907679428758, 360581908752202244, 360581910635234996, 360581912518324787]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 35090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 35000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 35000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk350B
