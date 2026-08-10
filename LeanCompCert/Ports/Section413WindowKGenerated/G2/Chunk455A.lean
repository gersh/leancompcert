import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk455A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk455A
