import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk183

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362530226830026995, 362530231278868132⟩, ⟨(-811675696684808740), (-811620629710795616)⟩, true⟩

def state01 : KState := ⟨⟨362502312508596521, 362502316962460202⟩, ⟨(-300585076810161823), (-300529917897971849)⟩, true⟩

def words00 : List Nat := [371285888257622198, 371285889691361064, 371285891119971928, 371285892548631242, 371285894123613289, 371285894340454599, 371285897541068334, 371285900741556591, 371285903531079318, 371285904428032920]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 18300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 18300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362552432188570164, 362552436647543956⟩, ⟨(-1218359995705987645), (-1218304743202112649)⟩, true⟩

def words01 : List Nat := [371285908308161464, 371285912188173179, 371285919050601542, 371285921941593110, 371285923738536148, 371285925535447239, 371285929241643080, 371285931665717337, 371285935296291930, 371285938926720742]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 18310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 18300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362561389846835854, 362561394310901709⟩, ⟨(-1382763849518429913), (-1382708503702059631)⟩, true⟩

def words02 : List Nat := [371285942695061710, 371285942695626212, 371285944869012578, 371285947242091153, 371285950499692361, 371285952451795675, 371285954019272359, 371285955586773185, 371285960131111793, 371285964246873448]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 18320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 18300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499773204529302, 362499777673681159⟩, ⟨(-252834502507532119), (-252779063438635025)⟩, true⟩

def words03 : List Nat := [371285970441073802, 371285976634821527, 371285981988858994, 371285983873106532, 371285986480189349, 371285989087272608, 371285993224522030, 371285993984116864, 371285994736103889, 371285995488225697]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 18330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 18300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362498889342649844, 362498893816855794⟩, ⟨(-236413649220718934), (-236358117433426474)⟩, true⟩

def words04 : List Nat := [371285999213633042, 371286001469644573, 371286004900487526, 371286008331187360, 371286011291434537, 371286011291999908, 371286010501014030, 371286010707899589, 371286013264911276, 371286013967396178]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 18340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 18300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362517642554338672, 362517647033711520⟩, ⟨(-580449590120750173), (-580393963496045605)⟩, true⟩

def words05 : List Nat := [371286014656322393, 371286015345367882, 371286019003827506, 371286021954401070, 371286025797943696, 371286029641281151, 371286033246726075, 371286033439087760, 371286035161348136, 371286036883747137]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 18350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 18300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480874519193049, 362480879003613489⟩, ⟨94656091816747651, 94711811141512933⟩, true⟩

def words06 : List Nat := [371286039350685302, 371286039351251395, 371286037867972081, 371286036376288671, 371286034884556982, 371286034287414171, 371286033107717670, 371286034000944301, 371286034790238785, 371286034790828596]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 18360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 18300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362533606191087599, 362533610680612169⟩, ⟨(-874237765879604408), (-874181952765181022)⟩, true⟩

def words07 : List Nat := [371286037194053660, 371286039877920360, 371286044680821439, 371286045538671538, 371286045663340790, 371286045788169084, 371286046878863598, 371286046879492956, 371286049093868434, 371286051682039449]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 18370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 18300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488036638872691, 362488041133514260⟩, ⟨(-36413168839318940), (-36357261648037486)⟩, true⟩

def words08 : List Nat := [371286053634852703, 371286053865355309, 371286056461944714, 371286059058550690, 371286062548908308, 371286062895570045, 371286063081207234, 371286063267005529, 371286064120272108, 371286064228416765]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 18380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 18300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470156563532238, 362470161063290170⟩, ⟨292721087768786460, 292777089075371746⟩, true⟩

def words09 : List Nat := [371286066736742887, 371286069245036091, 371286071745473807, 371286071746042504, 371286071383565686, 371286071505452350, 371286074582871156, 371286074583438472, 371286073725782163, 371286072861609484]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 18390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 18300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 18300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk183
