import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk920A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603330728650825, 360603386459142765⟩, ⟨(-1974049672101722409), (-1970587426563738253)⟩, true⟩

def state01 : KState := ⟨⟨360600011326932429, 360600067070111119⟩, ⟨(-1668759590818383204), (-1665296178038569374)⟩, true⟩

def words00 : List Nat := [360581967399767584, 360581967442758100, 360581967603482354, 360581967764608563, 360581967895833449, 360581967934212276, 360581967935408664, 360581967914982231, 360581967990470876, 360581968188694348]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574187099680598, 360574242855383939⟩, ⟨707526918706589028, 710991483942468762⟩, true⟩

def words01 : List Nat := [360581968475145626, 360581968761845737, 360581968989130236, 360581969181971637, 360581969264248602, 360581969346865121, 360581969431448455, 360581969432779197, 360581969426604185, 360581969344016220]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589770445088681, 360589826213371560⟩, ⟨(-726502688704823951), (-723036965838052629)⟩, true⟩

def words02 : List Nat := [360581969261130392, 360581969265754505, 360581969369640315, 360581969473777458, 360581969477279768, 360581969501117381, 360581969560306311, 360581969619879793, 360581969676452802, 360581969763198922]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360591223053687270, 360591278834644805⟩, ⟨(-860188641555918333), (-856721752178279955)⟩, true⟩

def words03 : List Nat := [360581969790516877, 360581969817979549, 360581969963088939, 360581970168028092, 360581970326463453, 360581970485138625, 360581970554830532, 360581970584971030, 360581970687180333, 360581970789836750]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595750914840152, 360595806708345113⟩, ⟨(-1277000646559276597), (-1273532602254899543)⟩, true⟩

def words04 : List Nat := [360581971009926727, 360581971112512751, 360581971125283509, 360581971138166158, 360581971139280488, 360581971139154049, 360581971275883567, 360581971412874252, 360581971480409576, 360581971632112863]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk920A
