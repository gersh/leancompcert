import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk511A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567340789216898, 360567357199456341⟩, ⟨745780039793998786, 746346652101361280⟩, true⟩

def state01 : KState := ⟨⟨360619150903489707, 360619167320396969⟩, ⟨(-1901989884952589241), (-1901422931886635331)⟩, true⟩

def words00 : List Nat := [360581962534342224, 360581962825084551, 360581963229671688, 360581963634375594, 360581963710736349, 360581963912295562, 360581964066834692, 360581964221564853, 360581964757897488, 360581965486508244]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 51100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 51100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360603890805718390, 360603907229360963⟩, ⟨(-1121888490767963046), (-1121321193426575736)⟩, true⟩

def words01 : List Nat := [360581966019092155, 360581966551725962, 360581967369579851, 360581968483331931, 360581969501334141, 360581970519415177, 360581971246404889, 360581971720757002, 360581972150428837, 360581972580323844]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 51110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 51100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360562924438821293, 360562940869129309⟩, ⟨972446457022238622, 973014095134240154⟩, true⟩

def words02 : List Nat := [360581972912101793, 360581972912808704, 360581972862966027, 360581972621933587, 360581972380795989, 360581972033451910, 360581971879251313, 360581971708427009, 360581971537526207, 360581971068525637]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 51120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 51100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360605128068833243, 360605144505809344⟩, ⟨(-1185611564327038892), (-1185043585241733464)⟩, true⟩

def words03 : List Nat := [360581970706255560, 360581970716377527, 360581971107791059, 360581971283541886, 360581971284205052, 360581971101827751, 360581971117694184, 360581971513531323, 360581971967235411, 360581972421078077]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 51130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 51100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604948751379038, 360604965195097863⟩, ⟨(-1176477589930821997), (-1175909265990308103)⟩, true⟩

def words04 : List Nat := [360581972683682061, 360581973106580615, 360581973842959628, 360581974579517161, 360581975158575364, 360581975457235546, 360581975563305621, 360581975669444443, 360581975765819414, 360581976216075160]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 51140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 51100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk511A
