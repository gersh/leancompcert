import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk964A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360556730504397874, 360556791915637473⟩, ⟨2453518732849259027, 2457516208126242511⟩, true⟩

def state01 : KState := ⟨⟨360585391002072931, 360585452426514234⟩, ⟨(-309481407396673614), (-305482659411344172)⟩, true⟩

def words00 : List Nat := [360582284559044462, 360582284403777828, 360582284301686569, 360582284285946290, 360582284270063391, 360582284163416961, 360582284061044414, 360582283961103457, 360582283860731833, 360582283880814975]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 96400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 96400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591790914821260, 360591852352587493⟩, ⟨(-926583535050089401), (-922583502340569541)⟩, true⟩

def words01 : List Nat := [360582283882082484, 360582283833679089, 360582283811133424, 360582283892360717, 360582283904360020, 360582283916581538, 360582283917840243, 360582283875842246, 360582283967852134, 360582284068683151]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 96410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 96400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360588731594561868, 360588793045497367⟩, ⟨(-631623190669576500), (-627621888113610380)⟩, true⟩

def words02 : List Nat := [360582284200711668, 360582284270917507, 360582284286836683, 360582284302912220, 360582284304108118, 360582284235035370, 360582284330949974, 360582284427130839, 360582284469040332, 360582284537983045]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 96420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 96400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360597976702851468, 360598038167004010⟩, ⟨(-1523126396121460402), (-1519123818979597446)⟩, true⟩

def words03 : List Nat := [360582284714170071, 360582284890792373, 360582285148135627, 360582285373912025, 360582285507915160, 360582285642012361, 360582285789718348, 360582285991330852, 360582286155819417, 360582286320600721]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 96430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 96400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597314694383012, 360597376171861434⟩, ⟨(-1459381846050804211), (-1455377983696812049)⟩, true⟩

def words04 : List Nat := [360582286400385753, 360582286401784725, 360582286453179917, 360582286533640701, 360582286586260707, 360582286651627044, 360582286652879181, 360582286651173268, 360582286714756049, 360582286872800805]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 96440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 96400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk964A
