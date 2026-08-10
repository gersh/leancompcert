import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk536A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579411035132188, 360579429160690531⟩, ⟨135289719869074791, 135946147410074421⟩, true⟩

def state01 : KState := ⟨⟨360567222872351021, 360567241004986439⟩, ⟨788399934734414271, 789056741642589069⟩, true⟩

def words00 : List Nat := [360581965422756909, 360581965136063091, 360581964501891964, 360581963911781715, 360581963321489043, 360581962581225313, 360581961863552184, 360581960948853376, 360581960034046239, 360581959466871211]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360572736006934763, 360572754146588204⟩, ⟨492848099048907743, 493505282227947867⟩, true⟩

def words01 : List Nat := [360581959265737574, 360581959339289061, 360581959339970835, 360581959105121975, 360581958817650880, 360581958442776290, 360581958067697537, 360581958070657497, 360581958071320423, 360581957900452955]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591356922017192, 360591375068691023⟩, ⟨(-505699091033610161), (-505041531387796423)⟩, true⟩

def words02 : List Nat := [360581957729410740, 360581957755215000, 360581958207663803, 360581958660238285, 360581958775882718, 360581958776626873, 360581958545104375, 360581958222045975, 360581957922080362, 360581958098442701]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360602952219869018, 360602970373637863⟩, ⟨(-1127646790470106012), (-1126988850284011904)⟩, true⟩

def words03 : List Nat := [360581958099111941, 360581958044672268, 360581958282027283, 360581958844517876, 360581959201838242, 360581959559271356, 360581959702997541, 360581959748374320, 360581960140673052, 360581960533211995]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579148710860283, 360579166871642399⟩, ⟨149162026784699366, 149820343198174898⟩, true⟩

def words04 : List Nat := [360581960827193185, 360581960827937611, 360581960775045770, 360581960547794680, 360581960320430607, 360581960005682617, 360581959865857516, 360581959777614270, 360581959689286865, 360581959422307790]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk536A
