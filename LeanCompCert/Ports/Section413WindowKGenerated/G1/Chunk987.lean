import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk987

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480496736727024, 362480645199496509⟩, ⟨454562769519260540, 464455856731677152⟩, true⟩

def state01 : KState := ⟨⟨362470725221006232, 362470873714626685⟩, ⟨1419090517907089324, 1428986650272855034⟩, true⟩

def words00 : List Nat := [371285350931607233, 371285350935083961, 371285350876885819, 371285350799189039, 371285350720121262, 371285350667099210, 371285350561421241, 371285350484880536, 371285350407213347, 371285350329460774]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 98700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 98700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362495278821821557, 362495427346824724⟩, ⟨(-1004696787583959025), (-994797557273967187)⟩, true⟩

def words01 : List Nat := [371285350185155085, 371285350145394149, 371285350162442186, 371285350167532679, 371285350170215630, 371285350159840274, 371285350236615285, 371285350277773307, 371285350382208089, 371285350488230566]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 98710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 98700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362487040148890680, 362487188705237701⟩, ⟨(-191369884469077885), (-181467559734507961)⟩, true⟩

def words02 : List Nat := [371285350572621271, 371285350576105953, 371285350638694942, 371285350719616048, 371285350800749919, 371285350804218109, 371285350748739918, 371285350694344552, 371285350682811928, 371285350705422704]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 98720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 98700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479859449189547, 362480008036718850⟩, ⟨517664052646678116, 527569456163556448⟩, true⟩

def words03 : List Nat := [371285350829020190, 371285350953996650, 371285351077639128, 371285351081107441, 371285351067920584, 371285351060764189, 371285351142942413, 371285351146410768, 371285351103537263, 371285351053289273]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 98730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 98700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480456752962158, 362480605371569743⟩, ⟨458739358087165374, 468647830432468344⟩, true⟩

def words04 : List Nat := [371285351043210547, 371285351051486894, 371285351133584197, 371285351217118746, 371285351275197346, 371285351278666324, 371285351210412627, 371285351184378335, 371285351168788186, 371285351172384250]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 98740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 98700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483660341324121, 362483808991548748⟩, ⟨142359640020065705, 152271234710589093⟩, true⟩

def words05 : List Nat := [371285351126918195, 371285351082502408, 371285351036632422, 371285351035349355, 371285350986523311, 371285350969950912, 371285350952196993, 371285350935405829, 371285350833882063, 371285350822600901]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481935871142365, 362482084552327127⟩, ⟨312679038167593818, 322593690638333946⟩, true⟩

def words06 : List Nat := [371285350849012414, 371285350852494428, 371285350815361163, 371285350759361412, 371285350702064197, 371285350677093023, 371285350630610366, 371285350657568016, 371285350660179916, 371285350662387250]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500134025569834, 362500282738040236⟩, ⟨(-1484832935064236250), (-1474915192349046628)⟩, true⟩

def words07 : List Nat := [371285350683390787, 371285350739222994, 371285350895820264, 371285350978941387, 371285351046213073, 371285351114567249, 371285351214216005, 371285351266682212, 371285351420193666, 371285351575242238]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488896678875232, 362489045422661144⟩, ⟨(-374786681152039521), (-364865844939925283)⟩, true⟩

def words08 : List Nat := [371285351726484739, 371285351742003820, 371285351848734266, 371285351957429345, 371285352076757738, 371285352080228205, 371285352063147353, 371285352036611831, 371285352070738913, 371285352112086903]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481449355093136, 362481598130195343⟩, ⟨360969965389606640, 370893895494151388⟩, true⟩

def words09 : List Nat := [371285352163567499, 371285352216435305, 371285352268054648, 371285352271526757, 371285352205036905, 371285352171097660, 371285352182717292, 371285352186249085, 371285352151008498, 371285352116991843]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk987
