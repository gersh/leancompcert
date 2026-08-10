import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk843A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk843B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk843A

def state06 : KState := ⟨⟨362481789631932389, 362481896783098762⟩, ⟨282776352550026028, 288879860029178244⟩, true⟩

def words05 : List Nat := [371285320858537202, 371285320855111546, 371285320963122926, 371285321020944406, 371285321120466333, 371285321221081266, 371285321297898434, 371285321300826726, 371285321190107912, 371285321153179715]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479986202389328, 362480093379647946⟩, ⟨434904904241975672, 441010612996439428⟩, true⟩

def words06 : List Nat := [371285321179984716, 371285321182913083, 371285321063257258, 371285320937775396, 371285320811142067, 371285320717353526, 371285320563072385, 371285320536401536, 371285320508703646, 371285320481852479]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491769805741304, 362491877009441854⟩, ⟨(-559371027916129743), (-553263088123465023)⟩, true⟩

def words07 : List Nat := [371285320421925300, 371285320388352484, 371285320444684853, 371285320447613939, 371285320354097984, 371285320239201283, 371285320145379204, 371285320148665695, 371285320202574282, 371285320283542381]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477564658861854, 362477671888984720⟩, ⟨639275967133452330, 645386136573460392⟩, true⟩

def words08 : List Nat := [371285320336770033, 371285320339701572, 371285320233912895, 371285320223096359, 371285320210790791, 371285320206995248, 371285320015316590, 371285319813845372, 371285319611203919, 371285319550278398]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362471879446492822, 362471986703062907⟩, ⟨1119136324939608749, 1125248726393854035⟩, true⟩

def words09 : List Nat := [371285319511374280, 371285319564387638, 371285319616305206, 371285319619234968, 371285319483880625, 371285319392781987, 371285319314465311, 371285319317401603, 371285319188576584, 371285319033944351]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk843B
