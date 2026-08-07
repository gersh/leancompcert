import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk604

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491987954388276, 362492041472345064⟩, ⟨(-413151388772736511), (-410967920800739279)⟩, true⟩

def state01 : KState := ⟨⟨362488463229671472, 362488516765942901⟩, ⟨(-200272963355920920), (-198088389083365450)⟩, true⟩

def words00 : List Nat := [371285237627909636, 371285237639813363, 371285237762952405, 371285237886876622, 371285237968625473, 371285237970670732, 371285237686790060, 371285237606281315, 371285237697589992, 371285237754023162]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494336806960728, 362494390361839328⟩, ⟨(-555099643091666106), (-552913944666092914)⟩, true⟩

def words01 : List Nat := [371285237807360258, 371285237861375227, 371285238188883224, 371285238380818561, 371285238640296860, 371285238900579136, 371285239105977244, 371285239108028518, 371285239185131238, 371285239339104417]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479727378345522, 362479780951441424⟩, ⟨327659641967623213, 329846441176900101⟩, true⟩

def words02 : List Nat := [371285239617386821, 371285239619432845, 371285239532612525, 371285239395273257, 371285239257088619, 371285239204909178, 371285239100654502, 371285239187146537, 371285239272030432, 371285239274148307]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499456337442449, 362499509929079722⟩, ⟨(-864679789621840640), (-862491869863484938)⟩, true⟩

def words03 : List Nat := [371285239185237418, 371285239164044786, 371285239356342129, 371285239377146208, 371285239378748801, 371285239338039219, 371285239434099535, 371285239473016625, 371285239710517199, 371285239948936054]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485908483864332, 362485962093957122⟩, ⟨(-45833716560459441), (-43644681257905187)⟩, true⟩

def words04 : List Nat := [371285240185668054, 371285240187715423, 371285240308107051, 371285240507084669, 371285240662119448, 371285240664166316, 371285240454310341, 371285240244314836, 371285240095225696, 371285240109519183]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362484412131815929, 362484465760338110⟩, ⟨44681463672460221, 46871613125896165⟩, true⟩

def words05 : List Nat := [371285240352609380, 371285240596549971, 371285240837187982, 371285240839235129, 371285240747618804, 371285240734853961, 371285240979679213, 371285241019292700, 371285241020849594, 371285241010307113]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 60450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 60400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489435595151494, 362489489241992527⟩, ⟨(-258994827587441317), (-256803570480091583)⟩, true⟩

def words06 : List Nat := [371285241220646767, 371285241308023692, 371285241574975591, 371285241842771736, 371285242060564583, 371285242062648368, 371285242127264084, 371285242201804935, 371285242446909947, 371285242519257992]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 60400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487004986970663, 362487058652544761⟩, ⟨(-112019932390345431), (-109827542407369181)⟩, true⟩

def words07 : List Nat := [371285242591777741, 371285242664990354, 371285242816359209, 371285242832399432, 371285242860015480, 371285242888404245, 371285242909547951, 371285242911609717, 371285242718318686, 371285242750982165]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 60470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 60400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472097000467441, 362472150684256657⟩, ⟨789724924697839745, 791918416427710733⟩, true⟩

def words08 : List Nat := [371285243009420447, 371285243011468492, 371285242905537107, 371285242799396231, 371285242692493129, 371285242668502523, 371285242531761877, 371285242507699345, 371285242482960660, 371285242408780177]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 60480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 60400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362511229540797168, 362511283243078811⟩, ⟨(-1577580848074852582), (-1575386237646006930)⟩, true⟩

def words09 : List Nat := [371285242223575402, 371285242255833404, 371285242560609408, 371285242686508517, 371285242753738784, 371285242821635440, 371285243162185781, 371285243367033399, 371285243798834288, 371285244231531134]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 60490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 60400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 60400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk604
