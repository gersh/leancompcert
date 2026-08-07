import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk018

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360727951976513993, 360727951991099587⟩, ⟨(-318303942363355149), (-318303924479416465)⟩, true⟩

def state01 : KState := ⟨⟨361051354131121454, 361051354145879030⟩, ⟨(-900826736780392352), (-900826718586021828)⟩, true⟩

def words00 : List Nat := [360551615077493434, 360551974562247704, 360552172469201064, 360552370156869030, 360552426784925688, 360552735280296656, 360553104107714398, 360553472527366114, 360553659826199362, 360553934643622806]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 1800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 1800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360976614444842327, 360976614459773069⟩, ⟨(-765574116898445733), (-765574098389780719)⟩, true⟩

def words01 : List Nat := [360554507937398956, 360555080598754724, 360555573690352980, 360555775074563982, 360555775074580934, 360555677623887594, 360555580280456364, 360555738099986283, 360555969350748368, 360556200347532663]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 1810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 1800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360712254996525339, 360712255011631042⟩, ⟨(-287029242661504702), (-287029223833516244)⟩, true⟩

def words02 : List Nat := [360556274521898633, 360556274521917012, 360556138714618034, 360556218003198731, 360556218003214201, 360556193407394521, 360556159625892561, 360555873331328116, 360555587349821580, 360555494102928958]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 1820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 1800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360019088523784431, 360019088539064473⟩, ⟨989020068084949926, 989020087232873302⟩, true⟩

def words03 : List Nat := [360555871444319885, 360556248373994274, 360556426417931165, 360556636929135270, 360556762026042825, 360556886986758435, 360557031523083115, 360557031523101665, 360556891740368206, 360556599456038861]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 1830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 1800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360967304986570431, 360967305002026478⟩, ⟨(-763115738122057671), (-763115718649399421)⟩, true⟩

def words04 : List Nat := [360556307489233476, 360555993064413647, 360555832711975167, 360555748604892635, 360555664588981781, 360555311140983348, 360554922812889134, 360554820813681691, 360554810018953479, 360555032868774507]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 1840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 1800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨359767933918757518, 359767933934391572⟩, ⟨1463908464801453935, 1463908484604345447⟩, true⟩

def words05 : List Nat := [360555106511948482, 360555180075639154, 360555324016145238, 360555627582783983, 360555714933708814, 360555802190558973, 360555802190575690, 360555742334247873, 360555404878213430, 360554981506759500]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 1850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 1800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360817409698942909, 360817409714754182⟩, ⟨(-493402901389646859), (-493402881256225629)⟩, true⟩

def words06 : List Nat := [360554558590293098, 360554417529715863, 360554367952820617, 360554136822142884, 360553905939323495, 360553594064731095, 360553549555330891, 360553667085908726, 360553667085925793, 360553698928406654]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 1860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 1800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362214326627718614, 362214326643708088⟩, ⟨(-3113957387976211362), (-3113957367508629754)⟩, true⟩

def words07 : List Nat := [360554118757839011, 360554538138980754, 360555235739753510, 360555659057756617, 360555840360172338, 360556021469406680, 360556480169438837, 360557084830203970, 360557966341822256, 360558846916164957]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 1870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 1800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361383943309894228, 361383943326064978⟩, ⟨(-1555675208101341198), (-1555675187292097340)⟩, true⟩

def words08 : List Nat := [360559497616730682, 360559876255336038, 360560230803716524, 360560584975923527, 360560751263320887, 360560872698680403, 360560872698697423, 360560768265715787, 360560834761338028, 360561270038232034]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 1880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 1800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360266178482053487, 360266178498404387⟩, ⟨563670228700388232, 563670249851040308⟩, true⟩

def words09 : List Nat := [360561812668228861, 360562354724927741, 360562753469745509, 360562883811182576, 360562934296340231, 360562984728276517, 360563013831295271, 360563013831314520, 360563003274504096, 360562847050957567]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 1890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 1800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 1800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk018
