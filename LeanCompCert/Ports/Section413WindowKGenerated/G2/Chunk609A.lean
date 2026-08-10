import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk609A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602494544759892, 360602518184756856⟩, ⟨(-1224575536257857692), (-1223602948958935256)⟩, true⟩

def state01 : KState := ⟨⟨360583910103136060, 360583933751155674⟩, ⟨(-92647553617970822), (-91674477698746652)⟩, true⟩

def words00 : List Nat := [360582427112366484, 360582427562262447, 360582427834839363, 360582428107494586, 360582428231676844, 360582428490458340, 360582428601175404, 360582428712035395, 360582428712795194, 360582428694963874]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360644962544369215, 360644986200442945⟩, ⟨(-3811737039758357571), (-3810763473224481633)⟩, true⟩

def words01 : List Nat := [360582428811088953, 360582428927468745, 360582429313044051, 360582429801916456, 360582430059431613, 360582430317004480, 360582430843833095, 360582431602221795, 360582432629743270, 360582433657424537]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360622417968583227, 360622441632797251⟩, ⟨(-2438287721429356830), (-2437313658948331568)⟩, true⟩

def words02 : List Nat := [360582434474099952, 360582435092170502, 360582435979449534, 360582436866949943, 360582437686217350, 360582438349495145, 360582438841936782, 360582439334471706, 360582439766413011, 360582440423906074]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573473516357320, 360573497188601283⟩, ⟨544168141709947777, 545142693496168907⟩, true⟩

def words03 : List Nat := [360582441079242830, 360582441734718153, 360582442228794715, 360582442454698910, 360582442497884286, 360582442541282151, 360582442853740434, 360582442898121754, 360582442898890261, 360582442752984220]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610189822030992, 360610213502340135⟩, ⟨(-1693445922870160063), (-1692470879552546067)⟩, true⟩

def words04 : List Nat := [360582442668422674, 360582442941397190, 360582443483355336, 360582444025463426, 360582444303262687, 360582444422675121, 360582444723034133, 360582445023642513, 360582445316391622, 360582445772859856]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk609A
