import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk148

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362503038814453819, 362503041669786970⟩, ⟨(-289026445332591710), (-288997858068652528)⟩, true⟩

def state01 : KState := ⟨⟨362522771292245705, 362522774151579077⟩, ⟨(-580981372311330786), (-580952725823182968)⟩, true⟩

def words00 : List Nat := [371283519912658930, 371283521452393116, 371283527025110884, 371283532597252697, 371283537105427510, 371283537567504420, 371283539553565054, 371283541539589309, 371283547093329236, 371283549742300623]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 14800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 14800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362503792521522591, 362503795384936251⟩, ⟨(-299518369770608956), (-299489662833020612)⟩, true⟩

def words01 : List Nat := [371283552364789443, 371283554987079174, 371283562158320256, 371283567044740749, 371283573335932212, 371283579626451005, 371283585101034713, 371283585541113674, 371283586905110707, 371283588269165857]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 14810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 14800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495476328538637, 362495479195940385⟩, ⟨(-176132162777124496), (-176103396715105724)⟩, true⟩

def words02 : List Nat := [371283594178802379, 371283594179250363, 371283594034396728, 371283593634835668, 371283594063284400, 371283594063786101, 371283596967714207, 371283600690699944, 371283604387876130, 371283605189014682]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 14820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 14800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362507788171356295, 362507791042821132⟩, ⟨(-358650579999244847), (-358621753661254661)⟩, true⟩

def words03 : List Nat := [371283610530201721, 371283615870910233, 371283622103026460, 371283622289661304, 371283622290009157, 371283621457525129, 371283623203776283, 371283623527093581, 371283625155939961, 371283626784775094]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 14830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 14800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472150868695815, 362472153744212836⟩, ⟨170156095842772718, 170184982335544524⟩, true⟩

def words04 : List Nat := [371283627456348000, 371283627456796853, 371283623109868734, 371283623204045017, 371283624695757224, 371283624696208112, 371283621892609318, 371283618012660010, 371283614133045360, 371283614012383580]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 14840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 14800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362517037809619370, 362517040689170613⟩, ⟨(-496404002976107059), (-496375056554018923)⟩, true⟩

def words05 : List Nat := [371283616998382119, 371283620755735754, 371283624489288721, 371283624489745315, 371283625875010909, 371283627267182362, 371283632590716441, 371283635004464721, 371283637252832799, 371283639501057161]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 14850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 14800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362538031113627358, 362538033997203974⟩, ⟨(-808525373408092517), (-808496367148164829)⟩, true⟩

def words06 : List Nat := [371283642304794602, 371283642857082730, 371283647133583601, 371283651409696586, 371283654932372663, 371283654932822121, 371283654460165003, 371283656483341576, 371283663023830484, 371283666680470186]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 14860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 14800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362545921320880319, 362545924208557341⟩, ⟨(-925839994829693018), (-925810927576534426)⟩, true⟩

def words07 : List Nat := [371283670313795936, 371283673946793439, 371283681489817957, 371283687079056172, 371283692121897998, 371283697164222612, 371283701879455384, 371283701879905350, 371283705731678973, 371283709913309943]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 14870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 14800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362507471970175610, 362507474861863026⟩, ⟨(-353369007025638565), (-353339880076560379)⟩, true⟩

def words08 : List Nat := [371283717300396914, 371283720963033912, 371283723393044141, 371283725822872585, 371283728900983401, 371283729722951048, 371283735052361508, 371283740381241921, 371283744849303616, 371283746443350062]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 14880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 14800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362657479050518415, 362657481946272807⟩, ⟨(-2587685333295436977), (-2587656145768817563)⟩, true⟩

def words09 : List Nat := [371283752543687700, 371283758643434479, 371283768509958564, 371283774386359439, 371283779473927341, 371283784560963755, 371283794150537966, 371283802091396281, 371283813748068595, 371283825403371739]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 14890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 14800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 14800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk148
