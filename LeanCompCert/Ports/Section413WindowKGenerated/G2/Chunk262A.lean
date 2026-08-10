import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk262A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360527564405319391, 360527568485937306⟩, ⟨1448439058774418800, 1448511378617481072⟩, true⟩

def state01 : KState := ⟨⟨360586277818724499, 360586281902590775⟩, ⟨(-90253357090435176), (-90180952123820130)⟩, true⟩

def words00 : List Nat := [360582853069962465, 360582850448760813, 360582848948278829, 360582848900684356, 360582848853066836, 360582847575744525, 360582844847707490, 360582843145940916, 360582841444192305, 360582841326034222]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 26200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 26200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360543126757595973, 360543130844733116⟩, ⟨1040955656809342835, 1041028147521398437⟩, true⟩

def words01 : List Nat := [360582841326340571, 360582840724561939, 360582840122765579, 360582840394099867, 360582840394392750, 360582840020030778, 360582839645662773, 360582838522288742, 360582835949322123, 360582834435408990]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 26210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 26200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576935402424322, 360576939492803732⟩, ⟨154255896623854250, 154328472364426398⟩, true⟩

def words02 : List Nat := [360582832921497962, 360582831823183097, 360582830775189641, 360582828995173199, 360582827215234689, 360582825056670534, 360582823941383563, 360582824108856834, 360582824109168551, 360582823155493951]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 26220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 26200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360636591503453267, 360636595597078568⟩, ⟨(-1410938115527073570), (-1410865454630332010)⟩, true⟩

def words03 : List Nat := [360582823179175417, 360582823427239472, 360582824488312855, 360582825151952450, 360582825152274673, 360582824410031230, 360582824373910871, 360582825808927654, 360582827858360111, 360582829907713440]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 26230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 26200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591870989750910, 360591875086658843⟩, ⟨(-237748176866047194), (-237675429817240058)⟩, true⟩

def words04 : List Nat := [360582831225649401, 360582831225993411, 360582831097009541, 360582830400777896, 360582829704505056, 360582828332481897, 360582826762253034, 360582824287016360, 360582821811901787, 360582821129483222]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 26240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 26200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk262A
