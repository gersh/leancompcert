import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk555A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482515221299647, 362482560105126591⟩, ⟨131782959954358136, 133465758030592246⟩, true⟩

def state01 : KState := ⟨⟨362479931528912366, 362479976429397830⟩, ⟨275182517036789505, 276866239747837281⟩, true⟩

def words00 : List Nat := [371284965132277435, 371284965134145118, 371284964984115205, 371284964771201240, 371284964557559669, 371284964376311818, 371284964104514618, 371284964107025555, 371284964109636019, 371284964111612708]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 55500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 55500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497919467604690, 362497964384979211⟩, ⟨(-723378192753729508), (-721693532445867090)⟩, true⟩

def words01 : List Nat := [371284964257170668, 371284964493577193, 371284964996121454, 371284965123935714, 371284965199264743, 371284965275155250, 371284965370311476, 371284965372374502, 371284965580036351, 371284965816285458]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 55510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 55500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490889033894880, 362490933968140614⟩, ⟨(-333050696191244525), (-331365099106683823)⟩, true⟩

def words02 : List Nat := [371284966068919047, 371284966075353251, 371284966297283499, 371284966520185324, 371284966837630100, 371284966839498826, 371284966725173106, 371284966592886679, 371284966649239984, 371284966758850188]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 55520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 55500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362465528131865116, 362465573082942778⟩, ⟨1075419489670561036, 1077106021518773090⟩, true⟩

def words03 : List Nat := [371284967002438259, 371284967246738125, 371284967480357270, 371284967482226196, 371284967284022789, 371284967143426379, 371284967018317384, 371284967020218976, 371284966768567806, 371284966421464903]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 55530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 55500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483528058512527, 362483573026303506⟩, ⟨75662190176086600, 77349650368000594⟩, true⟩

def words04 : List Nat := [371284966073561436, 371284966050110424, 371284965950228176, 371284966038995584, 371284966040469443, 371284966032261170, 371284965591894673, 371284965476088983, 371284965457303185, 371284965459253426]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 55540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 55500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk555A
