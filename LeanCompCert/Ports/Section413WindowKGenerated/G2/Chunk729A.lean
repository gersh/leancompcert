import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk729A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360607166096185422, 360607200458834380⟩, ⟨(-1810155144069855706), (-1808463136586876992)⟩, true⟩

def state01 : KState := ⟨⟨360612110307688952, 360612144680087001⟩, ⟨(-2170662231408775113), (-2168969513167077709)⟩, true⟩

def words00 : List Nat := [360582393877636874, 360582394219055855, 360582394444563750, 360582394670181206, 360582394765782074, 360582394980283861, 360582395382285129, 360582395784480649, 360582396091533248, 360582396500619334]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360604335361074983, 360604369743264928⟩, ⟨(-1603693102380206934), (-1601999670162211398)⟩, true⟩

def words01 : List Nat := [360582397097252796, 360582397694194874, 360582398355519983, 360582398829347800, 360582399142194157, 360582399455112357, 360582399762053198, 360582400163170160, 360582400465311542, 360582400767658968]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360619382653782907, 360619417045843280⟩, ⟨(-2701129308022430987), (-2699435156007091731)⟩, true⟩

def words02 : List Nat := [360582400962594749, 360582401106071469, 360582401437092774, 360582401768409237, 360582402052441019, 360582402342008671, 360582402505969457, 360582402670029133, 360582402987932649, 360582403496652853]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592831124363312, 360592865526185464⟩, ⟨(-764526901017077890), (-762832037024760636)⟩, true⟩

def words03 : List Nat := [360582404192706257, 360582404888938997, 360582405427535096, 360582405778633169, 360582406044669356, 360582406310982777, 360582406764657327, 360582407030949376, 360582407175258167, 360582407319730593]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581749010437919, 360581783422038727⟩, ⟨43815310937293789, 45510888234041339⟩, true⟩

def words04 : List Nat := [360582407414170818, 360582407603496196, 360582407786457675, 360582407969608352, 360582407994976101, 360582407996012636, 360582407833739833, 360582407588785335, 360582407343533469, 360582407286168050]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk729A
