import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk638A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360617613369143115, 360617639410289010⟩, ⟨(-2228995324077014857), (-2227872995855076709)⟩, true⟩

def state01 : KState := ⟨⟨360623702699459967, 360623728749151765⟩, ⟨(-2617635699880542208), (-2616512826387926962)⟩, true⟩

def words00 : List Nat := [360582720693414393, 360582721097083967, 360582721746105827, 360582722395375197, 360582722876123856, 360582723189107789, 360582723378358560, 360582723567701308, 360582724002367711, 360582724645997326]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 63800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 63800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584693146128954, 360584719204280818⟩, ⟨(-128210089425244134), (-127086676052489614)⟩, true⟩

def words01 : List Nat := [360582725326788360, 360582726007741153, 360582726548224192, 360582726844346637, 360582727078275992, 360582727312435782, 360582727617757448, 360582727841399292, 360582727873423160, 360582727905553871]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 63810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 63800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360630330459939166, 360630356526566455⟩, ⟨(-3040994141681103366), (-3039870187366386822)⟩, true⟩

def words02 : List Nat := [360582728043707658, 360582728371868714, 360582728945128811, 360582729518542812, 360582729845729534, 360582730252211404, 360582730846904566, 360582731441852521, 360582732051445794, 360582732798481882]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 63820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 63800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360608346665723141, 360608372740907103⟩, ⟨(-1637711659627013052), (-1636587159096983940)⟩, true⟩

def words03 : List Nat := [360582733421853666, 360582734045304033, 360582734540495629, 360582735158131557, 360582735629953516, 360582736101905133, 360582736416596032, 360582736573798124, 360582736976093037, 360582737378693213]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 63830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 63800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360601788260648742, 360601814344282457⟩, ⟨(-1218979324079841972), (-1217854284074014770)⟩, true⟩

def words04 : List Nat := [360582738026225081, 360582738490414056, 360582738802450895, 360582739114578187, 360582739355151084, 360582739720008907, 360582740076500728, 360582740433141749, 360582740666232633, 360582740965884719]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 63840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 63800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk638A
