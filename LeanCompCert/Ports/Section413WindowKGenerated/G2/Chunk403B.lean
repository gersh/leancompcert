import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk403A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk403B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk403A

def state06 : KState := ⟨⟨360532759774368948, 360532769815251135⟩, ⟨2013276299184702105, 2013550193450048215⟩, true⟩

def words05 : List Nat := [360582665241097487, 360582665400638509, 360582665401125935, 360582665253269249, 360582664493946571, 360582663313536633, 360582662133018122, 360582661565369657, 360582660797946236, 360582659562363377]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360572113758555329, 360572123804610663⟩, ⟨424883685107324550, 425157788185403848⟩, true⟩

def words06 : List Nat := [360582658326717983, 360582657703940106, 360582657859808325, 360582658172168061, 360582658172680895, 360582657913580918, 360582657043357284, 360582656524736537, 360582656005988584, 360582655332680651]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567558547432020, 360567568598696579⟩, ⟨608772903526227276, 609047216926492714⟩, true⟩

def words07 : List Nat := [360582655072299668, 360582654504848886, 360582653937321690, 360582653930426671, 360582653930887636, 360582653642250371, 360582653353558291, 360582652697250715, 360582651864545868, 360582651491636810]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360568963698571905, 360568973754995669⟩, ⟨551851939172251087, 552126460927231725⟩, true⟩

def words08 : List Nat := [360582651118567982, 360582650838092687, 360582650160926293, 360582649009382038, 360582647857805833, 360582646414336883, 360582645337281785, 360582644872165346, 360582644407011453, 360582643635186985]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579364853945972, 360579374915539562⟩, ⟨131648680208535743, 131923410798364451⟩, true⟩

def words09 : List Nat := [360582643297193204, 360582643097591219, 360582643064550042, 360582643065098867, 360582642970156201, 360582642354139953, 360582641738057534, 360582640929204645, 360582640426761786, 360582640346499918]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk403B
