import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk133

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360613570788825890, 360613571777718556⟩, ⟨(-427243263534724836), (-427234355617984052)⟩, true⟩

def state01 : KState := ⟨⟨360729163517169297, 360729164507613708⟩, ⟨(-1965265252338561336), (-1965256323775687798)⟩, true⟩

def words00 : List Nat := [360581457351096068, 360581466268235642, 360581478684199768, 360581491098328796, 360581498724225776, 360581500752542616, 360581502590572740, 360581504428372217, 360581511891080534, 360581522983778107]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 13300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 13300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360691133407258521, 360691134399272144⟩, ⟨(-1458727886708199776), (-1458718937251372476)⟩, true⟩

def words01 : List Nat := [360581529629571344, 360581536274382880, 360581548540865010, 360581565143711069, 360581580259341387, 360581595372728364, 360581606853239152, 360581612742875035, 360581620965355347, 360581629186656622]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 13310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 13300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360600185494397578, 360600186487965445⟩, ⟨(-247544394856815282), (-247535424689585782)⟩, true⟩

def words02 : List Nat := [360581634325215422, 360581634325380263, 360581633875673326, 360581630588466398, 360581627301726946, 360581620099495142, 360581617027321891, 360581618296911028, 360581618297059322, 360581618081642620]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 13320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 13300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360811351175454638, 360811352170579963⟩, ⟨(-3063687660560365486), (-3063678669624758194)⟩, true⟩

def words03 : List Nat := [360581625082902071, 360581632083160355, 360581642807761492, 360581650304620754, 360581652424501439, 360581654544074698, 360581662266169304, 360581673883325301, 360581691100721904, 360581708315574735]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 13330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 13300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360689532448871152, 360689533445569530⟩, ⟨(-1438301423052016922), (-1438292411123943576)⟩, true⟩

def words04 : List Nat := [360581722698441257, 360581737328581297, 360581752700056776, 360581768069275603, 360581779904477126, 360581786171865394, 360581789572558997, 360581792972759786, 360581796186121203, 360581804255911532]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 13340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 13300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360523114945467261, 360523115943721481⟩, ⟨784549637313742502, 784558670020103568⟩, true⟩

def words05 : List Nat := [360581813115181953, 360581821973156196, 360581828006752612, 360581833377001529, 360581837277112081, 360581841176686766, 360581845762089929, 360581845762255168, 360581844790771164, 360581840395070292]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 13350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 13300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360647446632680023, 360647447632497541⟩, ⟨(-877404093484192021), (-877395039884639345)⟩, true⟩

def words06 : List Nat := [360581835999990530, 360581837515051212, 360581838171755034, 360581838828390330, 360581838828545272, 360581833975343853, 360581826453826937, 360581824510604610, 360581823470776535, 360581828378897613]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 13360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 13300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360556123278600993, 360556124279993787⟩, ⟨344269728959196151, 344278803628072831⟩, true⟩

def words07 : List Nat := [360581830471479707, 360581832563766861, 360581837898771386, 360581846049916046, 360581852453444664, 360581858856044011, 360581860726774083, 360581860726939576, 360581857055321487, 360581855132282881]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 13370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 13300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570319821772612, 360570320824723480⟩, ⟨154095526243049860, 154104621766945500⟩, true⟩

def words08 : List Nat := [360581856850085544, 360581856850251070, 360581854950055095, 360581850205390612, 360581845461405472, 360581839260339591, 360581837022719515, 360581835536031813, 360581834049548207, 360581829758387928]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 13380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 13300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360733821558912465, 360733822563430378⟩, ⟨(-2036638280009765289), (-2036629163495517203)⟩, true⟩

def words09 : List Nat := [360581828899071453, 360581827859441521, 360581829031190299, 360581829031356080, 360581828429708453, 360581823160379531, 360581818170590678, 360581823968938558, 360581835312251543, 360581846653909036]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 13390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 13300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 13300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk133
