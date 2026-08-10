import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk649A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360523387948041737, 360523414931822832⟩, ⟨3862957072348192984, 3864140060676914438⟩, true⟩

def state01 : KState := ⟨⟨360566024682234490, 360566051674639966⟩, ⟨1095667453127495970, 1096851001221266388⟩, true⟩

def words00 : List Nat := [360582953923650936, 360582953244258533, 360582952715236320, 360582952327505383, 360582951939697273, 360582951350205954, 360582950800520110, 360582950411305486, 360582950021828022, 360582949702697604]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 64900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 64900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577611536907602, 360577638538022296⟩, ⟨343436300518386732, 344620413971915288⟩, true⟩

def words01 : List Nat := [360582949443205697, 360582948965322930, 360582948487279918, 360582948203664053, 360582948057576916, 360582947852222253, 360582947646781818, 360582947322518695, 360582947004669742, 360582946923942998]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 64910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 64900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594964644335085, 360594991654060255⟩, ⟨(-783196210965976367), (-782011538477348393)⟩, true⟩

def words02 : List Nat := [360582946997952729, 360582947243006149, 360582947291434558, 360582947339957187, 360582947340737084, 360582947213032855, 360582947431994622, 360582947660393584, 360582947735995292, 360582947922430104]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 64920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 64900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599900409421757, 360599927427790765⟩, ⟨(-1103734330902297852), (-1102549097127017958)⟩, true⟩

def words03 : List Nat := [360582948236137488, 360582948550120310, 360582948901292678, 360582949016176655, 360582949017033105, 360582948909671804, 360582948930555845, 360582949198874080, 360582949461071237, 360582949723457186]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 64930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 64900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360608178997644549, 360608206024723486⟩, ⟨(-1641515097210610462), (-1640329297769456314)⟩, true⟩

def words04 : List Nat := [360582949866968539, 360582949906787321, 360582950123138136, 360582950339767178, 360582950452901901, 360582950572716138, 360582950573723690, 360582950574835357, 360582950761203869, 360582951151083828]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 64940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 64900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk649A
