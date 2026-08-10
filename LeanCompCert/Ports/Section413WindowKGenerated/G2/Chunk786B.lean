import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk786A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk786B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk786A

def state06 : KState := ⟨⟨360574065081238425, 360574105329393485⟩, ⟨638540460499121190, 640678702304555110⟩, true⟩

def words05 : List Nat := [360582249687489552, 360582249655574553, 360582249751811289, 360582249962277417, 360582250132000426, 360582250301902359, 360582250376702594, 360582250377826307, 360582250342681016, 360582250240432191]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 78650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 78600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360573359587042833, 360573399845772911⟩, ⟨693988505186734108, 696127578877872874⟩, true⟩

def words06 : List Nat := [360582250137802274, 360582250060492452, 360582249890474824, 360582249618099565, 360582249345548030, 360582249032909029, 360582248844540562, 360582248773573698, 360582248702495417, 360582248550220323]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 78660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 78600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360576523247184353, 360576563516544510⟩, ⟨445081085470275316, 447220995479315838⟩, true⟩

def words07 : List Nat := [360582248454718288, 360582248472031382, 360582248484933296, 360582248486057133, 360582248370755123, 360582248119004714, 360582247867037781, 360582247703445827, 360582247636860619, 360582247565800730]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 78670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 78600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360544047624042283, 360544087904095657⟩, ⟨3000314893623457295, 3002455645028128549⟩, true⟩

def words08 : List Nat := [360582247494560409, 360582247342605278, 360582247029264119, 360582246677785203, 360582246326017120, 360582245934090871, 360582245380905134, 360582244703253902, 360582244025408991, 360582243395835753]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 78680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 78600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360552358805343013, 360552399095979085⟩, ⟨2346326464392093218, 2348468048602464302⟩, true⟩

def words09 : List Nat := [360582242911867024, 360582242589396850, 360582242266815015, 360582241831412970, 360582241491126387, 360582241110835723, 360582240730213214, 360582240511068029, 360582240236996291, 360582239858985470]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 78690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 78600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 78600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk786B
