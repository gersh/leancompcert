import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk148

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360628372659243365, 360628373896080822⟩, ⟨(-728719085543398066), (-728706690394964254)⟩, true⟩

def state01 : KState := ⟨⟨360684734919940322, 360684736158522134⟩, ⟨(-1563132130484354077), (-1563119709510741909)⟩, true⟩

def words00 : List Nat := [360579144214678782, 360579150418090557, 360579159856844495, 360579169294358514, 360579174482652433, 360579179034692392, 360579182196481100, 360579185357895492, 360579191275852099, 360579198402157896]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 14800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 14800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360621588490094947, 360621589730440915⟩, ⟨(-627266158683214351), (-627253711573825085)⟩, true⟩

def words01 : List Nat := [360579203226494405, 360579208050203019, 360579217407366439, 360579229125669943, 360579239695441132, 360579250263815696, 360579257366857202, 360579262062111298, 360579264918381816, 360579267774326360]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 14810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 14800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360667272046128303, 360667273288216846⟩, ⟨(-1304675351345163699), (-1304662878401889129)⟩, true⟩

def words02 : List Nat := [360579275160111359, 360579278040574211, 360579278276697410, 360579278512807670, 360579278512962891, 360579279925029231, 360579286955714155, 360579293985487279, 360579298717667833, 360579304649662340]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 14820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 14800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360618066875211592, 360618068119051370⟩, ⟨(-574657385605492506), (-574644886682636228)⟩, true⟩

def words03 : List Nat := [360579315105763154, 360579325560509822, 360579333853995067, 360579337648310265, 360579337648481350, 360579337140261315, 360579338588431337, 360579342807923661, 360579345417597428, 360579348026963059]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 14830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 14800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360613205412028673, 360613206657636086⟩, ⟨(-503030972177028469), (-503018447014132641)⟩, true⟩

def words04 : List Nat := [360579348027130290, 360579347089334498, 360579344988222115, 360579346197011785, 360579346263193174, 360579346263379485, 360579345150978770, 360579340347015766, 360579335543664528, 360579335642417304]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 14840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 14800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360660643664110303, 360660644911463900⟩, ⟨(-1207518857671468659), (-1207506306568855857)⟩, true⟩

def words05 : List Nat := [360579342436095635, 360579349228894529, 360579353735228589, 360579358398201565, 360579361923067768, 360579365447508270, 360579372129455861, 360579380606200226, 360579386075029102, 360579391543146233]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 14850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 14800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360729766138468733, 360729767387576300⟩, ⟨(-2235404122805340187), (-2235391545629843477)⟩, true⟩

def words06 : List Nat := [360579394538534900, 360579399784060226, 360579408066051084, 360579416346962967, 360579420743783639, 360579420743969378, 360579425087207344, 360579429509653647, 360579438433407743, 360579448542466365]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 14860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 14800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360715882728987424, 360715883979864107⟩, ⟨(-2028945326790255238), (-2028932723299364538)⟩, true⟩

def words07 : List Nat := [360579456371705785, 360579464199914646, 360579475203665705, 360579489491683112, 360579499727971927, 360579509962911643, 360579517140309022, 360579521809779582, 360579530974054398, 360579540137158687]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 14870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 14800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360718934581314919, 360718935833944318⟩, ⟨(-2074407571374724283), (-2074394941794420757)⟩, true⟩

def words08 : List Nat := [360579551321558229, 360579562652665595, 360579570168086739, 360579577682517198, 360579582524872458, 360579589695736828, 360579601356712430, 360579613016157027, 360579621196962572, 360579630552781575]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 14880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 14800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360914629549128106, 360914630803513594⟩, ⟨(-4989375444439351267), (-4989362788702220171)⟩, true⟩

def words09 : List Nat := [360579644397023083, 360579658239460049, 360579675003628949, 360579691118431132, 360579703303711752, 360579715487373028, 360579732155478047, 360579751765066855, 360579774240320802, 360579796712600084]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 14890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 14800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 14800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk148
