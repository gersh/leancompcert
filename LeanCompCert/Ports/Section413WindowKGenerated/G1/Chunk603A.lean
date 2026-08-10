import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk603A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489937823593856, 362489991157578697⟩, ⟨(-289720124283347808), (-287547759040284764)⟩, true⟩

def state01 : KState := ⟨⟨362486666931081041, 362486720283235602⟩, ⟨(-92431720220150384), (-90258259247603422)⟩, true⟩

def words00 : List Nat := [371285222927770928, 371285222993305821, 371285223057330827, 371285223122069567, 371285223202257041, 371285223204514901, 371285223364713104, 371285223536858188, 371285223709089004, 371285223736017888]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500695124803269, 362500748495473010⟩, ⟨(-938532408742934022), (-936357831029796356)⟩, true⟩

def words01 : List Nat := [371285223968603429, 371285224202299379, 371285224574762713, 371285224622396568, 371285224627960322, 371285224634147144, 371285224914776744, 371285225060784171, 371285225319545431, 371285225579224444]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489240846655286, 362489294235728594⟩, ⟨(-247592017073249332), (-245416329160943196)⟩, true⟩

def words02 : List Nat := [371285225837098049, 371285225839140279, 371285225865198309, 371285226002425413, 371285226192458235, 371285226194537901, 371285226194371631, 371285226195765570, 371285226334689409, 371285226404445159]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477708034927395, 362477761442401613⟩, ⟨448311997779468990, 450488795912982706⟩, true⟩

def words03 : List Nat := [371285226748374763, 371285227093105360, 371285227382682347, 371285227384725251, 371285227338890833, 371285227309825123, 371285227523180507, 371285227525223361, 371285227403989348, 371285227282572528]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362497720091900937, 362497773517647722⟩, ⟨(-759255858423281915), (-757077957631292053)⟩, true⟩

def words04 : List Nat := [371285227283570787, 371285227290043009, 371285227570664835, 371285227852131376, 371285228077849929, 371285228139913721, 371285228268041694, 371285228397177857, 371285228727493817, 371285228937481175]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk603A
