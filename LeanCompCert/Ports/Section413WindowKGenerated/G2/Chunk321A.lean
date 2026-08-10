import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk321A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360605354713218169, 360605360946407940⟩, ⟨(-752276324784987554), (-752141026372539748)⟩, true⟩

def state01 : KState := ⟨⟨360626716626796283, 360626722864017356⟩, ⟨(-1438106453905690862), (-1437971026068501346)⟩, true⟩

def words00 : List Nat := [360581931876976216, 360581933295434379, 360581934020554185, 360581934745671103, 360581935228254943, 360581936201992034, 360581937836035765, 360581939470060034, 360581940209381055, 360581941604446851]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360684483908214283, 360684490149469643⟩, ⟨(-3293462134910416016), (-3293326577512088976)⟩, true⟩

def words01 : List Nat := [360581943736195403, 360581945867940595, 360581948325196972, 360581949815031197, 360581950477667239, 360581951140303320, 360581952767835855, 360581954995730877, 360581958188329451, 360581961380828814]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360606218273308656, 360606224518645613⟩, ⟨(-779509822502511628), (-779374133984282348)⟩, true⟩

def words02 : List Nat := [360581963985002311, 360581965621979762, 360581966831938112, 360581968041938682, 360581968966530983, 360581968966958768, 360581968924559526, 360581968398860109, 360581967873112436, 360581968375544425]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360495524574555607, 360495530823918079⟩, ⟨2777692279495775673, 2777828097374722011⟩, true⟩

def words03 : List Nat := [360581968856950638, 360581969338406252, 360581969338787501, 360581969337185254, 360581968368917562, 360581967159002081, 360581965949040531, 360581964714672852, 360581962513863145, 360581959825080952]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360536709938972961, 360536716192376191⟩, ⟨1454005314615364034, 1454141262383946040⟩, true⟩

def words04 : List Nat := [360581957136369490, 360581955411568898, 360581954412834555, 360581954377807403, 360581954342741423, 360581953482742357, 360581951656518449, 360581949705835977, 360581947755145854, 360581946091672737]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk321A
