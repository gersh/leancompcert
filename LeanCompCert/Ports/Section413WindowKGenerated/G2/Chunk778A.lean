import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk778A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585670450542119, 360585709789365213⟩, ⟨(-274854632739540270), (-272787528681905372)⟩, true⟩

def state01 : KState := ⟨⟨360594244652700234, 360594284002005646⟩, ⟨(-941921548759059313), (-939853629127115783)⟩, true⟩

def words00 : List Nat := [360582203778969634, 360582204072856850, 360582204387093978, 360582204701529823, 360582204877540928, 360582204888821647, 360582204989012014, 360582205089524968, 360582205172566468, 360582205328950074]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 77800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 77800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598858631883178, 360598897991781388⟩, ⟨(-1300947577086384097), (-1298878833177670743)⟩, true⟩

def words01 : List Nat := [360582205378502116, 360582205428193004, 360582205642615343, 360582205985681841, 360582206266419886, 360582206547331839, 360582206745543274, 360582206965130945, 360582207180527304, 360582207396271466]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 77810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 77800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360603502465654978, 360603541836011382⟩, ⟨(-1662396122075406021), (-1660326564257912561)⟩, true⟩

def words02 : List Nat := [360582207723709167, 360582207924432035, 360582208041589912, 360582208158858856, 360582208170288468, 360582208327398264, 360582208613163082, 360582208899133289, 360582209102440674, 360582209377681695]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 77820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 77800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360613349852366290, 360613389233224900⟩, ⟨(-2428958674815351861), (-2426888299559081835)⟩, true⟩

def words03 : List Nat := [360582209701920653, 360582210026486718, 360582210346782311, 360582210502591984, 360582210517403746, 360582210532310046, 360582210686433436, 360582210923372658, 360582211324814608, 360582211726518164]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 77830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 77800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587378016506814, 360587417407958453⟩, ⟨(-407321396006294732), (-405250196137557110)⟩, true⟩

def words04 : List Nat := [360582212036982151, 360582212182905080, 360582212306481072, 360582212430381441, 360582212512654075, 360582212513765333, 360582212431485445, 360582212193399568, 360582211955106468, 360582211948861749]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 77840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 77800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk778A
