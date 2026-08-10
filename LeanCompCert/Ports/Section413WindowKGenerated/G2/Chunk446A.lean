import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk446A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585276052197299, 360585288414337102⟩, ⟨(-92543089753715147), (-92170499803799937)⟩, true⟩

def state01 : KState := ⟨⟨360545265398125334, 360545277766074093⟩, ⟨1691946627405702427, 1692319476463869493⟩, true⟩

def words00 : List Nat := [360583221858081198, 360583221652842385, 360583221186027442, 360583220697594023, 360583220209005988, 360583219389215320, 360583218067813825, 360583216494464882, 360583214921068260, 360583213643152414]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 44600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 44600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360516172082670264, 360516184456371860⟩, ⟨2989899980129003352, 2990273085850182864⟩, true⟩

def words01 : List Nat := [360583212793283835, 360583211932247049, 360583211071186031, 360583209957054600, 360583208341399347, 360583206597798078, 360583204854088617, 360583203612208042, 360583202387244981, 360583200885906826]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 44610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 44600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360554994299362249, 360555006678821456⟩, ⟨1257594703074800482, 1257968065728907326⟩, true⟩

def words02 : List Nat := [360583199384496931, 360583198384912356, 360583197750280421, 360583197617343881, 360583197484377615, 360583196828937989, 360583195848072004, 360583194944409159, 360583194040610431, 360583193281235279]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 44620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 44600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360551668409425631, 360551680794707418⟩, ⟨1406079355018530180, 1406452977562729880⟩, true⟩

def words03 : List Nat := [360583192650238564, 360583191679752804, 360583190709183230, 360583190240142632, 360583190071921858, 360583189713382678, 360583189354792930, 360583188744499061, 360583188062930035, 360583187357824863]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 44630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 44600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593664573864502, 360593676964896357⟩, ⟨(-468807344422408096), (-468433465166950996)⟩, true⟩

def words04 : List Nat := [360583186652542088, 360583186448563062, 360583186389602677, 360583186014264284, 360583185638843197, 360583185135526759, 360583185395459344, 360583185776292994, 360583185776845834, 360583185968834300]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 44640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 44600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk446A
