import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk141

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360520813217432490, 360520814334977908⟩, ⟨857142603509728197, 857153274520919493⟩, true⟩

def state01 : KState := ⟨⟨360572496886037471, 360572498005233096⟩, ⟨127964688632615728, 127975382920119258⟩, true⟩

def words00 : List Nat := [360581601036383707, 360581599747304707, 360581597845727231, 360581593401528322, 360581588957934298, 360581580198513381, 360581573988001418, 360581572780495213, 360581571573141180, 360581567841017655]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 14100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 14100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569234340451108, 360569235461305456⟩, ⟨173968471291407819, 173979188991793421⟩, true⟩

def words01 : List Nat := [360581569866856848, 360581572535123158, 360581575895114019, 360581575895289488, 360581574253693657, 360581568303355634, 360581562353827609, 360581558502555478, 360581557806119405, 360581556933613657]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 14110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 14100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583634167753619, 360583635290281249⟩, ⟨(-29992142921855736), (-29981401586557970)⟩, true⟩

def words02 : List Nat := [360581556061208006, 360581552613353961, 360581547152030615, 360581544271005034, 360581541390340221, 360581537051624078, 360581532949901948, 360581525331260785, 360581517713664738, 360581513614420620]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 14120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 14100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360406407789826907, 360406408914012045⟩, ⟨2475303253791660589, 2475314018555934841⟩, true⟩

def words03 : List Nat := [360581515174106684, 360581516733604788, 360581516733764081, 360581514472377441, 360581509776482847, 360581501685144306, 360581493594898991, 360581488720168861, 360581478863509295, 360581466482509636]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 14130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 14100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360545170318064527, 360545171443910500⟩, ⟨512631426324730560, 512642214581513192⟩, true⟩

def words04 : List Nat := [360581454103218672, 360581445092170078, 360581438614133445, 360581437109770781, 360581435605606164, 360581429164930833, 360581422099685611, 360581413267327984, 360581404436165884, 360581400575683046]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 14140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 14100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360532674277662305, 360532675405184994⟩, ⟨689586341101044930, 689597153091742450⟩, true⟩

def words05 : List Nat := [360581398015658337, 360581392467236484, 360581386919565128, 360581389689046341, 360581390370092396, 360581391051070543, 360581391051230783, 360581387613867834, 360581379208437570, 360581375769103903]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 14150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 14100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360490680466035491, 360490681595220379⟩, ⟨1283957350197094938, 1283968185732901100⟩, true⟩

def words06 : List Nat := [360581372330201094, 360581366855048794, 360581358619435834, 360581347874932869, 360581337131918400, 360581325131529900, 360581315677618824, 360581309060188110, 360581302443668030, 360581293323218467]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 14160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 14100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360634242360239724, 360634243491088132⟩, ⟨(-751096869476125102), (-751086010359979182)⟩, true⟩

def words07 : List Nat := [360581286929195262, 360581283194910320, 360581280680426698, 360581280680603395, 360581279983032376, 360581274578709652, 360581269175115871, 360581271771292272, 360581275507100365, 360581279242420198]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 14170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 14100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360591155419471226, 360591156552001930⟩, ⟨(-140285669892563991), (-140274786913088401)⟩, true⟩

def words08 : List Nat := [360581279695076767, 360581280378424083, 360581282468055261, 360581284557444136, 360581285395659871, 360581285395836462, 360581283734475450, 360581279575777884, 360581275417635395, 360581271780885512]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 14180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 14100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360492607830727274, 360492608964920979⟩, ⟨1258703854504586956, 1258714761090287460⟩, true⟩

def words09 : List Nat := [360581274661526655, 360581277541795288, 360581277541954453, 360581277337968664, 360581274321526692, 360581268183771648, 360581262046825860, 360581260845571685, 360581257092147701, 360581250849504803]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 14190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 14100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 14100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk141
