import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk037

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360535728261093931, 360535728328096673⟩, ⟨69665023602392008, 69665192018358666⟩, true⟩

def state01 : KState := ⟨⟨361063440298122187, 361063440365507917⟩, ⟨(-1886241534200532610), (-1886241364365593952)⟩, true⟩

def words00 : List Nat := [360554618723572113, 360554722991512149, 360554805034647017, 360554887033501117, 360554909294738124, 360554913925172388, 360554925190966124, 360554936450696790, 360555019512536567, 360555156516312123]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 3700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 3700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361252276752117938, 361252276819890575⟩, ⟨(-2588763725056071109), (-2588763553783755839)⟩, true⟩

def words01 : List Nat := [360555256721067649, 360555356871852519, 360555493692836599, 360555667204880351, 360555821343642852, 360555975399474714, 360556069696090092, 360556185517368802, 360556372638719721, 360556559659507948]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 3710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 3700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361214063058910408, 361214063127066792⟩, ⟨(-2447073961332536905), (-2447073788630774347)⟩, true⟩

def words02 : List Nat := [360556799516377091, 360556968875100096, 360557086454026161, 360557203969827658, 360557297350492020, 360557436094983458, 360557645887083414, 360557855566671789, 360558011172968138, 360558187011111077]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 3720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 3700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361419001781244861, 361419001849787697⟩, ⟨(-3214798260758077013), (-3214798086612924435)⟩, true⟩

def words03 : List Nat := [360558320187857538, 360558453293263939, 360558657316191713, 360558791298981140, 360558864893964885, 360558938449564276, 360559041059283148, 360559200275330191, 360559430168832519, 360559659939439415]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 3730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 3700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360809839001150690, 360809839070083870⟩, ⟨(-935769942086653056), (-935769766479633840)⟩, true⟩

def words04 : List Nat := [360559840932373828, 360559952070402918, 360560089786407934, 360560227428878600, 360560314525784392, 360560331890810871, 360560331890847526, 360560313112249958, 360560300465642653, 360560366991576903]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 3740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 3700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨359812506757982012, 359812506827302882⟩, ⟨2810281623900362645, 2810281800963196145⟩, true⟩

def words05 : List Nat := [360560428324099996, 360560489623946684, 360560513851315204, 360560513851356275, 360560468601404923, 360560404268130142, 360560339969091036, 360560265177353886, 360560121033422425, 360559922199899477]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 3750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 3700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360914485631382107, 360914485701092208⟩, ⟨(-1339195448294022539), (-1339195269765742161)⟩, true⟩

def words06 : List Nat := [360559723472101879, 360559594772424278, 360559523390843950, 360559486273853053, 360559449176575897, 360559351050307463, 360559258899768063, 360559236522579432, 360559261491562430, 360559355690547063]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 3760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 3700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360636739808548922, 360636739878653259⟩, ⟨(-291315460895065512), (-291315280878600452)⟩, true⟩

def words07 : List Nat := [360559412943353107, 360559470165814629, 360559491806378787, 360559569885364093, 360559625500572488, 360559681086338084, 360559700911427494, 360559700911468816, 360559672343981182, 360559692726873677]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 3770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 3700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360434191193057388, 360434191263551675⟩, ⟨475126132985523552, 475126314478006738⟩, true⟩

def words08 : List Nat := [360559739843281326, 360559759974354079, 360559759974391181, 360559730799397328, 360559701639812706, 360559653500564591, 360559641081022960, 360559624255434404, 360559607438723024, 360559554407213419]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 3780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 3700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨361012621454753341, 361012621525640213⟩, ⟨(-1720603692751505000), (-1720603509769181686)⟩, true⟩

def words09 : List Nat := [360559521338625809, 360559504637605794, 360559540010308483, 360559597368184394, 360559597368223014, 360559582591599002, 360559621681766032, 360559711941522891, 360559831128289393, 360559950252351821]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 3790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 3700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 3700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk037
