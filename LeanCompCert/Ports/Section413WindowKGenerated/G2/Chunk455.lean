import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk455

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581121119085718, 360581134006327025⟩, ⟨96717854641401513, 97114101223801887⟩, true⟩

def state01 : KState := ⟨⟨360551676992126112, 360551689885299435⟩, ⟨1436412001612805820, 1436808518131062158⟩, true⟩

def words00 : List Nat := [360583268335825489, 360583267989730165, 360583267161772145, 360583266816278957, 360583266470630773, 360583265895890263, 360583265000807243, 360583263665790769, 360583262330714578, 360583261155748371]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 45500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 45500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360544204916999082, 360544217816040305⟩, ⟨1776571342440049372, 1776968126037071018⟩, true⟩

def words01 : List Nat := [360583260462546270, 360583260109103575, 360583259755616151, 360583259095443254, 360583258451676222, 360583257685497772, 360583256919171049, 360583256373291745, 360583255758364545, 360583254901410188]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 45510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 45500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592518604151886, 360592531509090570⟩, ⟨(-422940377074520513), (-422543324996438067)⟩, true⟩

def words02 : List Nat := [360583254044361200, 360583253164934134, 360583252530195959, 360583252377352663, 360583252224466777, 360583251655350964, 360583251217784342, 360583251107632871, 360583250997295116, 360583251165478604]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 45520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 45500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360563210399131594, 360563223310011734⟩, ⟨911715169940211065, 912112492561600281⟩, true⟩

def words03 : List Nat := [360583251166039371, 360583251128361922, 360583251533784630, 360583252219237465, 360583252573192047, 360583252927223853, 360583252988672906, 360583252989296761, 360583252569758546, 360583252130665261]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 45530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 45500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575081704921986, 360575094621680664⟩, ⟨371094695291401765, 371492285651164931⟩, true⟩

def words04 : List Nat := [360583251733011462, 360583251791493369, 360583251792052030, 360583251468087349, 360583251144035174, 360583250697792128, 360583250562376220, 360583250632670347, 360583250633241636, 360583250324988045]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 45540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 45500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360595340968122443, 360595353890771085⟩, ⟨(-551942333222900574), (-551544474545925958)⟩, true⟩

def words05 : List Nat := [360583250146450783, 360583249837744067, 360583249700646130, 360583249701270259, 360583249393047755, 360583248676086339, 360583247959026224, 360583247731130248, 360583247997354462, 360583248263709653]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 45550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 45500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577534948487198, 360577547877088504⟩, ⟨259212045030856739, 259610174939793373⟩, true⟩

def words06 : List Nat := [360583248288175434, 360583248446759563, 360583248449459227, 360583248452332219, 360583248452857219, 360583248191756450, 360583247450206921, 360583246416701634, 360583245383122210, 360583244830675070]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 45560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 45500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360523696959053208, 360523709893531869⟩, ⟨2712975580523853650, 2713373978293688304⟩, true⟩

def words07 : List Nat := [360583244966929593, 360583245228304833, 360583245228864816, 360583245121858144, 360583244534483971, 360583243822907819, 360583243111183146, 360583242187887516, 360583241123897083, 360583239818461525]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 45570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 45500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588542075057311, 360588555015427305⟩, ⟨(-243055337565330451), (-242656671239530393)⟩, true⟩

def words08 : List Nat := [360583238512942634, 360583237419211178, 360583236615023284, 360583236160191058, 360583235705320094, 360583234838300261, 360583233755622057, 360583233153637759, 360583232551496328, 360583232546711122]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 45580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 45500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360600429902552231, 360600442848880905⟩, ⟨(-785172041313383130), (-784773103301855696)⟩, true⟩

def words09 : List Nat := [360583232547279888, 360583232265639813, 360583232069240657, 360583232508568745, 360583232631398180, 360583232754320616, 360583232754877241, 360583232636570084, 360583232911690400, 360583233289807599]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 45590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 45500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 45500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk455
