import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk377

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362520368364804407, 362520388435937388⟩, ⟨(-1339531656246571519), (-1339020298706605689)⟩, true⟩

def state01 : KState := ⟨⟨362501352115739302, 362501372197986258⟩, ⟨(-622543629098706663), (-622031852503741537)⟩, true⟩

def words00 : List Nat := [371284872469088541, 371284872759349394, 371284873589264375, 371284874419781879, 371284875461144057, 371284875788490952, 371284876114159946, 371284876440224424, 371284877053306088, 371284877492131104]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 37700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 37700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483146617370783, 362483166710707342⟩, ⟨64204135884242261, 64716330724580685⟩, true⟩

def words01 : List Nat := [371284878503786373, 371284879515903480, 371284880510928334, 371284880680253531, 371284881006750458, 371284881333847210, 371284882363792864, 371284882457221680, 371284882458157689, 371284882414066955]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 37710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 37700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362501583746938978, 362501603851315580⟩, ⟨(-631341943119865164), (-630829331793320636)⟩, true⟩

def words02 : List Nat := [371284882900958455, 371284883083617322, 371284883392523205, 371284883701884970, 371284883901512626, 371284883902749508, 371284883540692861, 371284883651670810, 371284884281184716, 371284884725615405]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 37720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 37700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362497518566577623, 362497538682137768⟩, ⟨(-477862760772298608), (-477349727433409506)⟩, true⟩

def words03 : List Nat := [371284885168223088, 371284885611211456, 371284886632294748, 371284887378878821, 371284888336333034, 371284889294218712, 371284890098948999, 371284890100180390, 371284890304167162, 371284890640818423]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 37730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 37700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478891934423529, 362478912060949876⟩, ⟨225182557962283715, 225696005222471881⟩, true⟩

def words04 : List Nat := [371284891246409287, 371284891247641083, 371284891028675830, 371284890740591012, 371284890452011059, 371284890375408989, 371284890217390951, 371284890490412896, 371284890761798515, 371284890763074975]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 37740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 37700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362506133418459130, 362506153556154434⟩, ⟨(-803370969145142475), (-802857100203536187)⟩, true⟩

def words05 : List Nat := [371284890734189228, 371284890864319153, 371284891501621336, 371284891502853762, 371284891331523265, 371284891047435331, 371284890913089018, 371284890914471818, 371284891449344555, 371284892013817009]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 37750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 37700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474574807083087, 362474594955879614⟩, ⟨388329224105540966, 388843512287436300⟩, true⟩

def words06 : List Nat := [371284892512457314, 371284892513689874, 371284892190259176, 371284892206108851, 371284892242345206, 371284892243579572, 371284891524907401, 371284890805589699, 371284890085798646, 371284889991947590]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 37760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 37700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477431980756726, 362477452140663694⟩, ⟨280531037564664392, 281045745444626832⟩, true⟩

def words07 : List Nat := [371284890061548426, 371284890404211307, 371284890736172352, 371284890737417033, 371284890688461534, 371284890770772491, 371284891392139115, 371284891393378075, 371284891344813440, 371284891149277898]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 37770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 37700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362502146552259408, 362502166723191075⟩, ⟨(-653175687667534801), (-652660563216518411)⟩, true⟩

def words08 : List Nat := [371284891457093478, 371284891612901180, 371284892468894156, 371284893325353707, 371284893943220717, 371284893982362491, 371284894539596459, 371284895097425438, 371284896000474438, 371284896458757308]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 37780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 37700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496572247983938, 362496592430200358⟩, ⟨(-442494347133116543), (-441978796178352275)⟩, true⟩

def words09 : List Nat := [371284896862614993, 371284897266867139, 371284897957394793, 371284898299147122, 371284898851650379, 371284899404594140, 371284899947299876, 371284899948533718, 371284899867872736, 371284900178773720]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 37790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 37700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 37700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk377
